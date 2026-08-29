#include "UsrAI.h"
#include<set>
#include <iostream>
#include<unordered_map>
#include<list>
#include <cstdlib>

using namespace std;
tagGame tagUsrGame;
ins UsrIns;
/*##########DO NOT MODIFY THE CODE ABOVE##########*/

/*============================================================================
 * AI v4.3 —— 祭司转化强化版（针对 v4.2 的 3 项问题重写）
 *
 * 前提事实（以头文件 / config.json 为准）：
 *   - 我方初始即工具时代（DefaultCivilization=2），"升时代"指升铜器：
 *     花费 800 食物、耗时 60 秒（1500帧），前置 = 市场 + 靶场建成
 *   - 初始资源：木200 食500 石300 金0；每房屋 +4 人口
 *   - 敌方波次（enemyai.cpp）：第一波6000帧、第二波13500帧、第三波21000帧出生
 *   - 祭司：HumanAction(祭司,敌军)=转换（冷却20秒，ConvertCooldown==0可发）；
 *           HumanAction(祭司,友军)=治疗（需贴邻，内核自动走近）
 *   - 建造校验要求落点已探索；exploredUpdate 首帧给全量、之后每帧增量
 *
 * v4.3 对 v4.2 的修复（对应用户 3 条）：
 *   1. 祭司转化强化：冷却就绪即转化最近敌军；射程放开到12格（配置值）；
 *      射程外主动走近到10格转化；转化后立刻返回三塔火力交集点（质心）。
 *   2. 祭司躲避点改为三塔质心：所有已建成箭塔的几何中心，确保始终处于
 *      最多箭塔的交叉火力下；箭塔索敌优先级改为"攻击祭司的敌军优先"。
 *   3. 第一波后节奏修正：箭塔强化科技一下令即解除资源冻结，立刻开始
 *      兵营造兵；硬性配额门控——棍棒兵<4时只造棍棒兵，弓箭手<2时只造
 *      弓箭手，两者都达标后才解锁阔剑兵/复合弓兵等其他单位。
 *
 * 早期版本要点沿用：
 *   - 新箭塔围绕"开局预置箭塔"螺旋就近选址
 *   - 所有建造点下达前校验整块占地已探索+平地+无重叠；失败坐标永久拉黑
 *   - 升铜器前不采金、不采石；食物采集优先级：浆果 > 羚羊/大象 > 农田
 *   - 市场+靶场建成且食物≥800 立即升铜器
 *   - 村民永不发呆：无本职资源时依次转木材→食物→(铜器后石/金)→开视野
 *
 * 本文件按阶段组织，后期策略可在各 manage* 中增量扩展。
 *==========================================================================*/
#include <map>
#include <vector>
#include <cmath>

tagInfo info;

/*----------------------------------------------------------------------------
 * 常量（波次时间来自 enemyai.cpp；花费来自 config.json）
 *--------------------------------------------------------------------------*/
static const int WAVE1_SPAWN = 6000;
static const int WAVE2_SPAWN = 13500;
static const int WAVE3_SPAWN = 21000;

static const int BRONZE_FOOD      = 800;   // 升铜器花费
static const int TOWER_STONE_COST = 150;   // 单座箭塔石料
static const int VILL_FOOD_COST   = 50;    // 村民花费
static const int PRE_VILL_TARGET  = 12;    // 升铜器前村民数
static const int POST_VILL_TARGET = 18;    // 第一波后(4棍棒2弓达标后)村民数
static const int LATE_VILL_TARGET = 28;    // 第二波结束后村民数
static const int LATE_FRAME       = 17500; // 第二波结束判定的固定帧
static const int SAVE_FRAME       = 8500;  // 第一波结束，进入"攒资源升箭塔"阶段
static const int CLUBS_NEED       = 4;     // 阶段C达标：棍棒兵数
static const int ARCHERS_NEED     = 2;     // 阶段C达标：弓箭手数
static const int PRIEST_CONVERT_DIS = 12;  // 祭司转化射程（config.json DIS_PRIEST）
static const int PRE_FARM_MAX     = 4;     // 升铜器前农田上限
static const int POST_FARM_MAX    = 8;     // 升铜器后农田上限
static const int TOWER_TARGET     = 3;     // 第一波前箭塔数

/*----------------------------------------------------------------------------
 * 基地锚点
 *--------------------------------------------------------------------------*/
static double s_bls = 35.777;              // 块边长（首帧读取）
static int s_tcDR = -1, s_tcUR = -1;       // 市镇中心块坐标
static int s_twDR = -1, s_twUR = -1;       // 开局预置箭塔块坐标（塔簇锚点）

/*----------------------------------------------------------------------------
 * 探索集合与探索边界（前线）
 *--------------------------------------------------------------------------*/
static set<int> s_explored;                // key = DR*1000+UR
static vector<pair<int,int> > s_frontier;  // 已探索且紧邻未探索的块
static int s_frontierFrame = -9999;        // 上次重建帧

/*----------------------------------------------------------------------------
 * 建造：双在途槽位 + 坐标黑名单
 *--------------------------------------------------------------------------*/
struct PendBuild { int id; int type; int dr; int ur; int frame; int builderSN; };
static PendBuild s_pend[2];
static set<int> s_badSpot;                 // 永久拉黑的建造块
static map<int,int> s_spotSkipUntil;       // 临时跳过的建造块 -> 截止帧
static map<int,int> s_buildTypeCdUntil;    // 建筑类型 -> 失败冷却截止帧（防报错刷屏）

/*----------------------------------------------------------------------------
 * 科技状态机（一次性科技，经 ins_ret 确认）
 *--------------------------------------------------------------------------*/
struct ResearchState { int id; int frame; int cdUntil; bool done; };
enum { R_TOWER_UNLOCK = 0,   // 谷仓：解锁箭塔（50食/10秒）——升级前唯一允许的科技
       R_TOWER_UPG,          // 谷仓：箭塔强化（铜器）
       R_WOOD,               // 市场：木材加工（铜器）
       R_FARM,               // 市场：驯养动物（铜器）
       R_STONE,              // 市场：石矿开采（铜器）
       R_GOLD,               // 市场：金矿开采（铜器）
       R_USETOOL,            // 仓库：工具使用 近战攻+2（铜器）
       R_CLUB,               // 兵营：棍棒兵升战斧（铜器）
       R_NUM };
static ResearchState s_res[R_NUM];

/*----------------------------------------------------------------------------
 * 升级时代跟踪
 *--------------------------------------------------------------------------*/
static bool s_ageUpgOrdered = false;
static int  s_ageUpgId = -1;
static int  s_ageUpgFrame = 0;
static int  s_ageUpgCdUntil = 0;
static int  s_lastUpgradeTry = -9999;

/*----------------------------------------------------------------------------
 * 村民生产与状态
 *--------------------------------------------------------------------------*/
static int s_villPending = 0;              // 在生产队列中的村民数
static int s_lastFarmerCnt = 0;
static int s_lastVillOrderFrame = -9999;   // 上次造村民下令帧（队列超时兜底）

static map<int,char> s_farmerRole;         // SN -> 'F'/'W'/'S'/'G'
static map<int,int>  s_lastFleeFrame;
static map<int,int>  s_farmerCmdFrame;
static map<int,int>  s_farmerCmdId;
static map<int,int>  s_farmerCmdTarget;
static map<int,char> s_farmerCmdKind;      // 'G'采集 'D'上交 'M'移动
static map<int,int>  s_farmerStuck;
static map<int,int>  s_targetBadUntil;     // 目标SN -> 拉黑截止帧

/*----------------------------------------------------------------------------
 * 祭司状态
 *--------------------------------------------------------------------------*/
static int s_priestCmdFrame = -999;        // 上次移动指令帧
static int s_priestCmdId = -1;             // 上次移动指令id
static int s_priestMoveKey = -1;           // 上次移动目标块key
static map<int,int> s_scoutBad;            // 块key -> 拉黑截止帧
static double s_priestSnapDR = 0, s_priestSnapUR = 0;
static int s_lastPriestBlood = -1;         // 上一帧祭司血量（掉血检测）
static int s_priestHurtFrame = -9999;      // 上次掉血帧（判定"正被攻击"）
static int s_priestSnapFrame = 0;
static int s_priestSnapKey = -1;
static int s_priestSkillFrame = -999;      // 上次技能(转换/治疗)指令帧

/* v4.3 问题2：祭司躲塔卡位检测
 * 内核的移动指令不做路径可达性校验（Core_List.cpp:225 只记录目的地就返回
 * 成功），目的地走不到时祭司原地不动且无错误码——因此不能依赖 ins_ret，
 * 必须靠"位移快照"判断是否卡住：
 *   s_shelterTries  连续躲塔失败次数（300帧位移<0.8格算一次失败）
 *   >=3 次后放弃躲塔，降级为"原地转化+向远离敌人方向撤离" */
static int s_shelterTries = 0;             // 连续躲塔失败次数
static int s_shelterMoveFrame = -9999;     // 上次躲塔移动下令帧（快照起点）
static double s_shelterSnapDR = 0, s_shelterSnapUR = 0;  // 快照位置

/*----------------------------------------------------------------------------
 * 军队/箭塔指令冷却
 *--------------------------------------------------------------------------*/
static map<int,int> s_armyCmdFrame;
static map<int,int> s_towerCmdFrame;
static int s_trainCdFrame = 0;

/*----------------------------------------------------------------------------
 * 通用小工具
 *--------------------------------------------------------------------------*/
static double dist2(double dr1, double ur1, double dr2, double ur2)
{
    double a = dr1 - dr2, b = ur1 - ur2;
    return a * a + b * b;
}

static double blockCenter(int b) { return (b + 0.5) * s_bls; }

static int bkey(int dr, int ur) { return dr * 1000 + ur; }

static void clampDetail(double& x, double& y)
{
    int bx = (int)(x / s_bls), by = (int)(y / s_bls);
    if (bx < 2) bx = 2;
    if (bx > MAP_L - 3) bx = MAP_L - 3;
    if (by < 2) by = 2;
    if (by > MAP_U - 3) by = MAP_U - 3;
    x = blockCenter(bx);
    y = blockCenter(by);
}

static bool isBronze(const tagInfo& inf)
{
    return inf.civilizationStage >= CIVILIZATION_BRONZEAGE;
}

static int countAnyBuilding(const tagInfo& inf, int type)
{
    int n = 0;
    for (size_t i = 0; i < inf.buildings.size(); ++i)
        if (inf.buildings[i].Type == type) ++n;
    return n;
}

static int countDoneBuilding(const tagInfo& inf, int type)
{
    int n = 0;
    for (size_t i = 0; i < inf.buildings.size(); ++i)
        if (inf.buildings[i].Type == type && inf.buildings[i].Percent >= 100) ++n;
    return n;
}

static int armyCountNonPriest(const tagInfo& inf)
{
    int n = 0;
    for (size_t i = 0; i < inf.armies.size(); ++i)
        if (inf.armies[i].Sort != AT_PRIEST) ++n;
    return n;
}

static int countArchers(const tagInfo& inf)
{
    int n = 0;
    for (size_t i = 0; i < inf.armies.size(); ++i) {
        int s = inf.armies[i].Sort;
        if (s == AT_BOWMAN || s == AT_COMPOSITE_BOWMAN || s == AT_CHARIOT_ARCHER)
            ++n;
    }
    return n;
}

static int countMelee(const tagInfo& inf)
{
    int n = 0;
    for (size_t i = 0; i < inf.armies.size(); ++i) {
        int s = inf.armies[i].Sort;
        if (s == AT_PRIEST || s == AT_BOWMAN || s == AT_COMPOSITE_BOWMAN ||
            s == AT_CHARIOT_ARCHER)
            continue;
        ++n;
    }
    return n;
}

/* v4.3：棍棒兵数量（阶段C门控：4棍棒+2弓达标后才恢复村民生产） */
static int countClubs(const tagInfo& inf)
{
    int n = 0;
    for (size_t i = 0; i < inf.armies.size(); ++i)
        if (inf.armies[i].Sort == AT_CLUBMAN) ++n;
    return n;
}

/* v4.3 村民目标（阶段式）：
 *   升铜器前：12
 *   升铜器后~箭塔强化下令前：维持12（攒资源）
 *   箭塔强化下令后~第二波结束：需先达成"4棍棒+2弓"（阶段C），达标才升到18；
 *     未达标维持12，避免与造兵抢食物。
 *   第二波结束后：28 */
static int villTarget(const tagInfo& inf)
{
    if (!isBronze(inf)) return PRE_VILL_TARGET;
    if (inf.GameFrame >= LATE_FRAME) return LATE_VILL_TARGET;
    /* 阶段C门控：4棍棒+2弓达标后才恢复扩村民到18 */
    if (countClubs(inf) >= CLUBS_NEED && countArchers(inf) >= ARCHERS_NEED)
        return POST_VILL_TARGET;
    return PRE_VILL_TARGET;
}

static const tagArmy* findPriest(const tagInfo& inf)
{
    for (size_t i = 0; i < inf.armies.size(); ++i)
        if (inf.armies[i].Sort == AT_PRIEST) return &inf.armies[i];
    return NULL;
}

static const tagArmy* nearestEnemy(const tagInfo& inf, double dr, double ur)
{
    const tagArmy* best = NULL;
    double bd = 1e18;
    for (size_t i = 0; i < inf.enemy_armies.size(); ++i) {
        double d = dist2(dr, ur, inf.enemy_armies[i].DR, inf.enemy_armies[i].UR);
        if (d < bd) { bd = d; best = &inf.enemy_armies[i]; }
    }
    return best;
}

static const tagBuilding* nearestBuilding(const tagInfo& inf, int type,
                                          double dr, double ur, bool doneOnly)
{
    const tagBuilding* best = NULL;
    double bd = 1e18;
    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        const tagBuilding& b = inf.buildings[i];
        if ((int)b.Type != type) continue;
        if (doneOnly && b.Percent < 100) continue;
        double d = dist2(dr, ur, blockCenter(b.BlockDR), blockCenter(b.BlockUR));
        if (d < bd) { bd = d; best = &b; }
    }
    return best;
}

static bool targetBad(const tagInfo& inf, int sn)
{
    map<int,int>::const_iterator it = s_targetBadUntil.find(sn);
    return it != s_targetBadUntil.end() && inf.GameFrame < it->second;
}

static void noteFarmerCmd(int sn, int id, int target, char kind, int frame)
{
    s_farmerCmdId[sn]     = id;
    s_farmerCmdTarget[sn] = target;
    s_farmerCmdKind[sn]   = kind;
    s_farmerCmdFrame[sn]  = frame;
}

/* 清理已阵亡/消失村民的状态记录 */
static void cleanFarmerMaps(const tagInfo& inf)
{
    set<int> alive;
    for (size_t i = 0; i < inf.farmers.size(); ++i)
        alive.insert(inf.farmers[i].SN);

    vector<int> dead;
    for (map<int,char>::iterator it = s_farmerRole.begin();
         it != s_farmerRole.end(); ++it)
        if (!alive.count(it->first)) dead.push_back(it->first);
    for (size_t k = 0; k < dead.size(); ++k) {
        int sn = dead[k];
        s_farmerRole.erase(sn);
        s_farmerCmdFrame.erase(sn);
        s_farmerCmdId.erase(sn);
        s_farmerCmdTarget.erase(sn);
        s_farmerCmdKind.erase(sn);
        s_farmerStuck.erase(sn);
        s_lastFleeFrame.erase(sn);
    }
}

/*----------------------------------------------------------------------------
 * 探索集合维护
 *--------------------------------------------------------------------------*/
static void seedExploredFromMap(const tagInfo& inf);   // 前向声明
static bool s_seedDone = false;

static void updateExplored(const tagInfo& inf)
{
    size_t before = s_explored.size();
    for (size_t i = 0; i < inf.exploredUpdate.size(); ++i)
        s_explored.insert(bkey(inf.exploredUpdate[i].x,
                               inf.exploredUpdate[i].y));
    /* 补全初始已探索区域（内核首帧前已探索块不会经 exploredUpdate 下发）；
     * playerMap 当帧已含全部已探索块，扫一次即可 */
    if (!s_seedDone && inf.theMap) {
        seedExploredFromMap(inf);
        s_seedDone = true;
    }
    /* 探索集变化或超过600帧 -> 重建前线 */
    if (s_explored.size() != before ||
        inf.GameFrame - s_frontierFrame >= 600) {
        s_frontier.clear();
        static const int dxs[4] = { 1, -1, 0, 0 };
        static const int dys[4] = { 0, 0, 1, -1 };
        for (set<int>::const_iterator it = s_explored.begin();
             it != s_explored.end() && s_frontier.size() < 800; ++it) {
            int dr = (*it) / 1000, ur = (*it) % 1000;
            for (int d = 0; d < 4; ++d) {
                int nr = dr + dxs[d], nu = ur + dys[d];
                if (nr < 0 || nr >= MAP_L || nu < 0 || nu >= MAP_U) continue;
                if (!s_explored.count(bkey(nr, nu))) {
                    s_frontier.push_back(make_pair(dr, ur));
                    break;
                }
            }
        }
        s_frontierFrame = inf.GameFrame;
    }
}

/* 探索判定（双口径，均与内核 Explored 对齐）：
 *   1) 增量探索集 s_explored（exploredUpdate 累积）
 *   2) theMap 类型 != UNKNOWN：playerMap 只对已探索块填真实地形，
 *      未探索块恒为 UNKNOWN —— 可补上"初始已探索区域"（内核从不
 *      通过 exploredUpdate 下发首帧前的已探索块，v4 祭司不探路、
 *      建造报未探索的根因） */
static bool isExplored(const tagInfo& inf, int dr, int ur)
{
    if (dr < 0 || dr >= MAP_L || ur < 0 || ur >= MAP_U) return false;
    if (s_explored.count(bkey(dr, ur))) return true;
    if (inf.theMap && (*inf.theMap)[dr][ur].type != MAPPATTERN_UNKNOWN)
        return true;
    return false;
}

static bool areaExplored(const tagInfo& inf, int dr, int ur, int w)
{
    for (int i = 0; i < w; ++i)
        for (int j = 0; j < w; ++j)
            if (!isExplored(inf, dr + i, ur + j)) return false;
    return true;
}

/* 从 theMap 补全初始已探索区域（供前线/边界生成使用） */
static void seedExploredFromMap(const tagInfo& inf)
{
    if (!inf.theMap) return;
    for (int i = 0; i < MAP_L; ++i)
        for (int j = 0; j < MAP_U; ++j)
            if ((*inf.theMap)[i][j].type != MAPPATTERN_UNKNOWN)
                s_explored.insert(bkey(i, j));
}

/*----------------------------------------------------------------------------
 * 建造选址
 *--------------------------------------------------------------------------*/
static int bsize(int type)
{
    /* 房屋/箭塔/船坞 2x2，其余 3x3（Building.cpp 地基表） */
    if (type == BUILDING_HOME || type == BUILDING_ARROWTOWER ||
        type == BUILDING_DOCK)
        return 2;
    return 3;
}

/* 占地校验：边界 + 整块已探索(向外1圈缓冲) + 平地（无海洋、无高度差）
 * 内核只校验左上角块是否探索，但实际"未探索"误报多发生在边缘块，
 * 预检向外扩1圈作为缓冲，减少撞墙 */
static bool areaBuildable(const tagInfo& inf, int dr, int ur, int w)
{
    if (dr < 1 || ur < 1 || dr + w > MAP_L - 1 || ur + w > MAP_U - 1)
        return false;
    if (!areaExplored(inf, dr - 1, ur - 1, w + 2)) return false;
    if (inf.theMap == NULL) return true;   // 拿不到地形时只依赖探索校验
    int h0 = (*inf.theMap)[dr][ur].height;
    if (h0 < 0 || h0 >= MAPHEIGHT_OCEAN) return false;
    for (int i = 0; i < w; ++i) {
        for (int j = 0; j < w; ++j) {
            const tagTerrain& t = (*inf.theMap)[dr + i][ur + j];
            if (t.height != h0) return false;
            if (t.type == MAPPATTERN_OCEAN) return false;
        }
    }
    return true;
}

/* 占地与已有建筑/在途建筑/静态资源不重叠 */
static bool areaFree(const tagInfo& inf, int dr, int ur, int w)
{
    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        const tagBuilding& b = inf.buildings[i];
        int bw = bsize(b.Type);
        if (dr < b.BlockDR + bw && b.BlockDR < dr + w &&
            ur < b.BlockUR + bw && b.BlockUR < ur + w)
            return false;
    }
    for (int k = 0; k < 2; ++k) {
        if (s_pend[k].id < 0 || s_pend[k].type < 0) continue;
        int bw = bsize(s_pend[k].type);
        if (dr < s_pend[k].dr + bw && s_pend[k].dr < dr + w &&
            ur < s_pend[k].ur + bw && s_pend[k].ur < ur + w)
            return false;
    }
    /* 静态资源占地（树/浆果/石/金，约2x2） */
    for (size_t i = 0; i < inf.resources.size(); ++i) {
        const tagResource& r = inf.resources[i];
        if (r.Type != RESOURCE_TREE && r.Type != RESOURCE_BUSH &&
            r.Type != RESOURCE_STONE && r.Type != RESOURCE_GOLD)
            continue;
        if (r.Cnt <= 0) continue;
        if (dr < r.BlockDR + 2 && r.BlockDR < dr + w &&
            ur < r.BlockUR + 2 && r.BlockUR < ur + w)
            return false;
    }
    /* 动物占地（羚羊/大象/狮子等会走动，约2x2缓冲）——v4.1 修复
     * 截图"重叠"报错根因：预检漏掉动物，内核按 map_Object 判重叠 */
    for (size_t i = 0; i < inf.resources.size(); ++i) {
        const tagResource& r = inf.resources[i];
        if (r.Type != RESOURCE_GAZELLE && r.Type != RESOURCE_ELEPHANT &&
            r.Type != RESOURCE_LION)
            continue;
        if (r.Cnt <= 0) continue;
        if (dr < r.BlockDR + 2 && r.BlockDR < dr + w &&
            ur < r.BlockUR + 2 && r.BlockUR < ur + w)
            return false;
    }
    return true;
}

/* 围绕锚点螺旋搜索第一个合法建造位（确定顺序，失败拉黑后自动换下一格） */
static bool findBuildSpot(const tagInfo& inf, int type,
                          int adr, int aur, int& odr, int& our_)
{
    int w = bsize(type);
    for (int r = 1; r <= 18; ++r) {
        for (int dx = -r; dx <= r; ++dx) {
            for (int dy = -r; dy <= r; ++dy) {
                int mx = abs(dx), my = abs(dy);
                if ((mx > my ? mx : my) != r) continue;   // 只扫当前环
                int dr = adr + dx, ur = aur + dy;
                int key = bkey(dr, ur);
                if (s_badSpot.count(key)) continue;
                map<int,int>::const_iterator sk = s_spotSkipUntil.find(key);
                if (sk != s_spotSkipUntil.end() && inf.GameFrame < sk->second)
                    continue;
                if (!areaBuildable(inf, dr, ur, w)) continue;
                if (!areaFree(inf, dr, ur, w)) continue;
                odr = dr; our_ = ur;
                return true;
            }
        }
    }
    return false;
}

/* v4.3 问题6：箭塔专用选址——在 findBuildSpot 基础上增加塔间距约束：
 * 候选位与所有已有箭塔（含在建）间距 ≥4 格，即塔之间至少隔 2 个空格。
 * 目的：扩大火力覆盖范围；避免第三波投石车一次溅射命中两塔。 */
static bool findBuildSpotTower(const tagInfo& inf,
                               int adr, int aur, int& odr, int& our_)
{
    const int w = bsize(BUILDING_ARROWTOWER);      // 2x2
    const double minGap = 4.0 * s_bls;             // 塔间距下限
    for (int r = 1; r <= 18; ++r) {
        for (int dx = -r; dx <= r; ++dx) {
            for (int dy = -r; dy <= r; ++dy) {
                int mx = abs(dx), my = abs(dy);
                if ((mx > my ? mx : my) != r) continue;   // 只扫当前环
                int dr = adr + dx, ur = aur + dy;
                int key = bkey(dr, ur);
                if (s_badSpot.count(key)) continue;
                map<int,int>::const_iterator sk = s_spotSkipUntil.find(key);
                if (sk != s_spotSkipUntil.end() && inf.GameFrame < sk->second)
                    continue;
                if (!areaBuildable(inf, dr, ur, w)) continue;
                if (!areaFree(inf, dr, ur, w)) continue;
                /* 塔间距校验：候选塔中心与每座已有箭塔中心距离≥4格 */
                double cx = blockCenter(dr) + 0.5 * s_bls;   // 2x2塔中心
                double cy = blockCenter(ur) + 0.5 * s_bls;
                bool gapOk = true;
                for (size_t i = 0; i < inf.buildings.size() && gapOk; ++i) {
                    const tagBuilding& b = inf.buildings[i];
                    if (b.Type != BUILDING_ARROWTOWER) continue;
                    double bx = blockCenter(b.BlockDR) + 0.5 * s_bls;
                    double by = blockCenter(b.BlockUR) + 0.5 * s_bls;
                    if (dist2(cx, cy, bx, by) < minGap * minGap)
                        gapOk = false;
                }
                if (!gapOk) continue;
                odr = dr; our_ = ur;
                return true;
            }
        }
    }
    return false;
}

/*----------------------------------------------------------------------------
 * 村民分工（分阶段配额）
 *   升铜器前：食物 + 木材；石头仅当箭塔缺石时临时征用；不采金
 *   升铜器后：木6(研发后4) 金2 石按需，其余食物
 *--------------------------------------------------------------------------*/
static char getRoleSN(int sn)
{
    map<int,char>::const_iterator it = s_farmerRole.find(sn);
    return (it != s_farmerRole.end()) ? it->second : 'F';
}

static int villagerCount(const tagInfo& inf)
{
    int n = 0;
    for (size_t i = 0; i < inf.farmers.size(); ++i)
        if (inf.farmers[i].FarmerSort == FARMERTYPE_FARMER) ++n;
    return n;
}

static char pickRole(const tagInfo& inf)
{
    bool bronze = isBronze(inf);

    /* 石头需求：缺的箭塔数 x 150 - 库存（铜器后加箭塔强化50石） */
    int towersBuilt = countAnyBuilding(inf, BUILDING_ARROWTOWER);
    int stoneNeed = TOWER_STONE_COST * (TOWER_TARGET - towersBuilt);
    if (bronze && towersBuilt >= TOWER_TARGET && !s_res[R_TOWER_UPG].done)
        stoneNeed += 50;
    stoneNeed -= inf.Stone;
    if (stoneNeed < 0) stoneNeed = 0;

    /* v4.2 问题6：升铜器后安排少部分村民采石（固定1~2人），
     * 石头花销优先级由科技门控保证：谷仓强化 > 采石科技 */
    int qS = 0;
    if (!bronze && stoneNeed > 0) qS = (stoneNeed > 100) ? 3 : 2;
    else if (bronze) qS = (stoneNeed > 0 || !s_res[R_STONE].done) ? 2 : 1;
    int qG = bronze ? 2 : 0;
    int qW = bronze ? (s_res[R_WOOD].done ? 4 : 6) : 5;

    int cF = 0, cW = 0, cS = 0, cG = 0;
    for (size_t i = 0; i < inf.farmers.size(); ++i) {
        if (inf.farmers[i].FarmerSort != FARMERTYPE_FARMER) continue;
        char r = getRoleSN(inf.farmers[i].SN);
        if (r == 'F') ++cF;
        else if (r == 'W') ++cW;
        else if (r == 'S') ++cS;
        else if (r == 'G') ++cG;
    }

    int total = villagerCount(inf);
    int qF = total - qW - qS - qG;
    if (qF < 4) qF = 4;

    int dF = qF - cF, dW = qW - cW, dS = qS - cS, dG = qG - cG;
    char best = 'F';
    int bd = dF;
    if (dS > bd) { bd = dS; best = 'S'; }
    if (dG > bd) { bd = dG; best = 'G'; }
    if (dW > bd) { bd = dW; best = 'W'; }
    return best;
}

/* 统计某资源/农田上正在工作的村民数 */
static int workersOnTarget(const tagInfo& inf, int targetSN, int selfSN)
{
    int n = 0;
    for (size_t i = 0; i < inf.farmers.size(); ++i) {
        const tagFarmer& f = inf.farmers[i];
        if (f.SN == selfSN) continue;
        if (f.NowState == HUMAN_STATE_IDLE) continue;
        if (f.WorkObjectSN == targetSN) { ++n; continue; }
        map<int,int>::const_iterator it = s_farmerCmdTarget.find(f.SN);
        if (it != s_farmerCmdTarget.end() && it->second == targetSN) ++n;
    }
    return n;
}

static int resCap(int resType)
{
    switch (resType) {
    case RESOURCE_TREE:     return 2;
    case RESOURCE_BUSH:     return 3;
    case RESOURCE_STONE:    return 3;
    case RESOURCE_GOLD:     return 2;
    case RESOURCE_GAZELLE:  return 2;
    case RESOURCE_ELEPHANT: return 3;
    default:                return 3;
    }
}

/* 按资源类型找最近可用资源 */
static int nearestResOfType(const tagInfo& inf, double dr, double ur,
                            int type, int selfSN, int cap)
{
    int sn = -1;
    double bd = 1e18;
    for (size_t i = 0; i < inf.resources.size(); ++i) {
        const tagResource& r = inf.resources[i];
        if ((int)r.Type != type || r.Cnt <= 0) continue;
        if (targetBad(inf, r.SN)) continue;
        if (workersOnTarget(inf, r.SN, selfSN) >= cap) continue;
        double d = dist2(dr, ur, r.DR, r.UR);
        if (d < bd) { bd = d; sn = r.SN; }
    }
    return sn;
}

/* 食物目标：浆果 > 羚羊/大象 > 农田（1人1田） */
static int nearestFoodSN(const tagInfo& inf, double dr, double ur, int selfSN)
{
    int sn = nearestResOfType(inf, dr, ur, RESOURCE_BUSH, selfSN,
                              resCap(RESOURCE_BUSH));
    if (sn >= 0) return sn;
    sn = nearestResOfType(inf, dr, ur, RESOURCE_GAZELLE, selfSN,
                          resCap(RESOURCE_GAZELLE));
    if (sn >= 0) return sn;
    sn = nearestResOfType(inf, dr, ur, RESOURCE_ELEPHANT, selfSN,
                          resCap(RESOURCE_ELEPHANT));
    if (sn >= 0) return sn;

    double bd = 1e18;
    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        const tagBuilding& b = inf.buildings[i];
        if (b.Type != BUILDING_FARM || b.Percent < 100 || b.Cnt <= 0) continue;
        if (targetBad(inf, b.SN)) continue;
        if (workersOnTarget(inf, b.SN, selfSN) >= 1) continue;
        double d = dist2(dr, ur, blockCenter(b.BlockDR), blockCenter(b.BlockUR));
        if (d < bd) { bd = d; sn = b.SN; }
    }
    return sn;
}

/* 按角色找资源（食物走优先级函数） */
static int resourceForRole(const tagInfo& inf, double dr, double ur,
                           char role, int selfSN)
{
    if (role == 'F') return nearestFoodSN(inf, dr, ur, selfSN);
    if (role == 'W') return nearestResOfType(inf, dr, ur, RESOURCE_TREE,
                                             selfSN, resCap(RESOURCE_TREE));
    if (role == 'S') return nearestResOfType(inf, dr, ur, RESOURCE_STONE,
                                             selfSN, resCap(RESOURCE_STONE));
    if (role == 'G') return nearestResOfType(inf, dr, ur, RESOURCE_GOLD,
                                             selfSN, resCap(RESOURCE_GOLD));
    return -1;
}

/* 找最近的探索边界块（用于发呆村民开视野 / 祭司探路） */
static bool nearestFrontier(const tagInfo& inf, double dr, double ur,
                            double minDist2, int& fdr, int& fur)
{
    double bd = 1e18;
    bool found = false;
    for (size_t i = 0; i < s_frontier.size(); ++i) {
        int kdr = s_frontier[i].first, kur = s_frontier[i].second;
        int key = bkey(kdr, kur);
        map<int,int>::const_iterator sb = s_scoutBad.find(key);
        if (sb != s_scoutBad.end() && inf.GameFrame < sb->second) continue;
        double tx = blockCenter(kdr), ty = blockCenter(kur);
        double d = dist2(dr, ur, tx, ty);
        if (d < minDist2) continue;
        if (d < bd) { bd = d; fdr = kdr; fur = kur; found = true; }
    }
    return found;
}

/*----------------------------------------------------------------------------
 * v4.2 辅助：烂尾续建节流 / 在途统计 / 远程资源簇 / 间隔选址
 *--------------------------------------------------------------------------*/
static map<int,int> s_fixCmdFrame;         // 建筑SN -> 上次续建下令帧

/* 远程资源簇：找距市镇中心>minDist、簇内≥minN个的type资源，返回其块坐标。
 * 用于"资源太远就在资源地建存放建筑"（问题11）。
 * v4.3 问题3：storeType 为待建的存放建筑类型——若该资源簇 8 格内
 * 已有同种存放建筑（含在建），说明此簇已被覆盖，跳过，避免重复修建。 */
static bool remoteCluster(const tagInfo& inf, int type, int minN,
                          double minDist, int storeType,
                          int& adr, int& aur)
{
    double tcx = blockCenter(s_tcDR), tcy = blockCenter(s_tcUR);
    double cl2 = 6.0 * s_bls * (6.0 * s_bls);
    double near2 = 8.0 * s_bls * (8.0 * s_bls);
    for (size_t i = 0; i < inf.resources.size(); ++i) {
        const tagResource& r0 = inf.resources[i];
        if ((int)r0.Type != type || r0.Cnt <= 0) continue;
        int cnt = 0;
        for (size_t j = 0; j < inf.resources.size(); ++j) {
            const tagResource& r1 = inf.resources[j];
            if ((int)r1.Type != type || r1.Cnt <= 0) continue;
            if (dist2(r0.DR, r0.UR, r1.DR, r1.UR) < cl2) ++cnt;
        }
        if (cnt < minN) continue;
        if (dist2(r0.DR, r0.UR, tcx, tcy) < minDist * minDist) continue;
        /* v4.3：簇中心8格内已有同种存放建筑 -> 该簇已覆盖，跳过 */
        bool covered = false;
        for (size_t j = 0; j < inf.buildings.size() && !covered; ++j) {
            const tagBuilding& b = inf.buildings[j];
            if ((int)b.Type != storeType) continue;
            if (dist2(r0.DR, r0.UR, blockCenter(b.BlockDR),
                      blockCenter(b.BlockUR)) < near2)
                covered = true;
        }
        if (covered) continue;
        adr = r0.BlockDR; aur = r0.BlockUR;
        return true;
    }
    return false;
}

/* 螺旋选址 + 与已有建筑保持≥gap间距（资源建筑防扎堆，问题11） */
static bool findBuildSpotGap(const tagInfo& inf, int type,
                             int adr, int aur, double gap,
                             int& odr, int& our_)
{
    int w = bsize(type);
    for (int r = 1; r <= 18; ++r) {
        for (int dx = -r; dx <= r; ++dx) {
            for (int dy = -r; dy <= r; ++dy) {
                int mx = abs(dx), my = abs(dy);
                if ((mx > my ? mx : my) != r) continue;
                int dr = adr + dx, ur = aur + dy;
                int key = bkey(dr, ur);
                if (s_badSpot.count(key)) continue;
                map<int,int>::const_iterator sk = s_spotSkipUntil.find(key);
                if (sk != s_spotSkipUntil.end() && inf.GameFrame < sk->second)
                    continue;
                if (!areaBuildable(inf, dr, ur, w)) continue;
                if (!areaFree(inf, dr, ur, w)) continue;
                /* 与所有已有建筑中心距≥gap */
                double cx = blockCenter(dr) + (w - 1) * 0.5 * s_bls;
                double cy = blockCenter(ur) + (w - 1) * 0.5 * s_bls;
                bool gapOk = true;
                for (size_t i = 0; i < inf.buildings.size() && gapOk; ++i) {
                    const tagBuilding& b = inf.buildings[i];
                    double bx = blockCenter(b.BlockDR);
                    double by = blockCenter(b.BlockUR);
                    if (dist2(cx, cy, bx, by) < gap * gap) gapOk = false;
                }
                if (!gapOk) continue;
                odr = dr; our_ = ur;
                return true;
            }
        }
    }
    return false;
}

/*----------------------------------------------------------------------------
 * 1. 建造管理
 *    优先级：箭塔(第一波前3座) > 房屋(按容量配套) > 兵营 > 市场 > 靶场 >
 *            农田(锚定谷仓) > 远程谷仓/仓库(资源太远时)
 *    选址：箭塔围绕开局预置箭塔，其余围绕市镇中心；螺旋就近。
 *    失败处理：永久拉黑该坐标，绝不重试同一位置。
 *    烂尾续建：在建建筑长期无建造者 -> 派空闲村民续建（问题8）。
 *--------------------------------------------------------------------------*/
void UsrAI::manageBuild(const tagInfo& inf)
{
    /* 1) 处理在途建造指令的结果 */
    for (int k = 0; k < 2; ++k) {
        if (s_pend[k].id < 0) continue;
        map<int,int>::const_iterator it = inf.ins_ret.find(s_pend[k].id);
        int res;
        bool hasRet = (it != inf.ins_ret.end());
        if (hasRet) res = it->second;
        else if (inf.GameFrame - s_pend[k].frame > 600) res = -1; // 超时
        else continue;

        /* 失败处理（v4.1）：
         *   LOCK(未解锁) -> 仅类型冷却，不拉黑坐标（位置没问题）
         *   地形/重叠/未探索/越界 -> 整块占地拉黑 + 类型冷却
         *   超时(建造者死亡) -> 临时跳过该块 */
        int w = bsize(s_pend[k].type < 0 ? BUILDING_HOME : s_pend[k].type);
        if (hasRet && res == ACTION_SUCCESS) {
            /* 成功：建筑实体出现后自然占用该位置 */
        } else if (hasRet) {
            if (res != ACTION_INVALID_HUMANBUILD_LOCK) {
                for (int i = 0; i < w; ++i)
                    for (int j = 0; j < w; ++j)
                        s_badSpot.insert(bkey(s_pend[k].dr + i, s_pend[k].ur + j));
            }
            s_buildTypeCdUntil[s_pend[k].type] = inf.GameFrame + 300;
        } else {
            int key = bkey(s_pend[k].dr, s_pend[k].ur);
            s_spotSkipUntil[key] = inf.GameFrame + 1200;
        }
        s_pend[k].id = -1;
        s_pend[k].type = -1;
        s_pend[k].builderSN = -1;
    }

    /* 1.5) v4.2 烂尾续建（问题8）：在建建筑长期无人建造时，
     *      派空闲村民对其 HumanAction -> 内核走 CoreEven_FixBuilding
     *      续建流程（Core.cpp:983）。敌袭赶跑建造者后建筑可续建完成。 */
    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        const tagBuilding& b = inf.buildings[i];
        if (b.Percent >= 100) continue;

        /* 是否已有人在建造 */
        bool hasWorker = false;
        for (size_t j = 0; j < inf.farmers.size() && !hasWorker; ++j) {
            const tagFarmer& f = inf.farmers[j];
            if (f.FarmerSort != FARMERTYPE_FARMER) continue;
            if (f.WorkObjectSN == b.SN && f.NowState != HUMAN_STATE_IDLE)
                hasWorker = true;
        }
        for (int k = 0; k < 2 && !hasWorker; ++k) {
            if (s_pend[k].id < 0 || s_pend[k].type != (int)b.Type) continue;
            for (size_t j = 0; j < inf.farmers.size(); ++j) {
                if (inf.farmers[j].SN == s_pend[k].builderSN &&
                    inf.farmers[j].NowState != HUMAN_STATE_IDLE) {
                    hasWorker = true;
                    break;
                }
            }
        }
        if (hasWorker) continue;

        /* 节流：同一建筑240帧内只下一次续建令 */
        int lastFix = -9999;
        map<int,int>::iterator fc = s_fixCmdFrame.find(b.SN);
        if (fc != s_fixCmdFrame.end()) lastFix = fc->second;
        if (inf.GameFrame - lastFix < 240) continue;

        const tagFarmer* fb = NULL;
        double bd2 = 1e18;
        double bx = blockCenter(b.BlockDR), by = blockCenter(b.BlockUR);
        for (size_t j = 0; j < inf.farmers.size(); ++j) {
            const tagFarmer& f = inf.farmers[j];
            if (f.FarmerSort != FARMERTYPE_FARMER) continue;
            if (f.NowState != HUMAN_STATE_IDLE) continue;
            double d = dist2(f.DR, f.UR, bx, by);
            if (d < bd2) { bd2 = d; fb = &f; }
        }
        if (!fb) continue;
        int id = HumanAction(fb->SN, b.SN);
        s_fixCmdFrame[b.SN] = inf.GameFrame;
        noteFarmerCmd(fb->SN, id, b.SN, 'M', inf.GameFrame);
    }

    /* 2) 找空闲槽位 */
    int slot = -1;
    for (int k = 0; k < 2; ++k)
        if (s_pend[k].id < 0) { slot = k; break; }
    if (slot < 0 || s_tcDR < 0) return;

    /* 同类型只允许一个在途 */
    bool typePend[16];
    for (int t = 0; t < 16; ++t) typePend[t] = false;
    for (int k = 0; k < 2; ++k)
        if (s_pend[k].id >= 0 && s_pend[k].type >= 0 && s_pend[k].type < 16)
            typePend[s_pend[k].type] = true;

    bool bronze = isBronze(inf);
    int farmMax = bronze ? POST_FARM_MAX : PRE_FARM_MAX;
    int vTarget = villTarget(inf);          // 三段式目标 12/20/28

    /* v4.3 问题1：房屋按"村民+兵力"总量配套，不超建。
     * 兵力目标与 manageBuildingActions 保持一致：
     *   升铜器前 3（1近战+2弓）/ 二波前 12 / 之后 20
     * 所需房屋 = (村民+兵力)/4 向上取整，例：
     *   12+3=15 -> 4座(16)；20+12=32 -> 8座；28+20=48 -> 12座 */
    int aTarget = !bronze ? 3 : (inf.GameFrame < WAVE3_SPAWN ? 12 : 20);
    int needHome = (vTarget + aTarget + 3) / 4;

    /* v4.3 问题4：农田触发只看"浆果"是否采空（瞪羚留给猎人），
     * 不再等浆果+瞪羚全部枯竭，避免农田修筑过晚 */
    int bushLeft = 0;
    for (size_t i = 0; i < inf.resources.size(); ++i) {
        if (inf.resources[i].Type == RESOURCE_BUSH &&
            inf.resources[i].Cnt > 0)
            ++bushLeft;
    }

    /* v4.1 建造顺序（内核前置实锤，见 Development.cpp）：
     *   市场前置=谷仓(初始有)；靶场前置=兵营；农田前置=市场
     *   顺序：箭塔 > 房屋(人口将满) > 兵营 > 市场 > 靶场 > 农田
     *   兵营提前到升铜器前，否则靶场永远未解锁 */
    int want = -1;
    int anchorDR = s_tcDR, anchorUR = s_tcUR;

    /* 类型冷却查询 lambda（C++11 无泛型 lambda，用函数对象简化） */
    #define TYPE_OK(T) \
        (!typePend[T] && \
         (s_buildTypeCdUntil.find(T) == s_buildTypeCdUntil.end() || \
          inf.GameFrame >= s_buildTypeCdUntil[T]))

    if (TYPE_OK(BUILDING_ARROWTOWER) &&
        countAnyBuilding(inf, BUILDING_ARROWTOWER) < TOWER_TARGET &&
        s_res[R_TOWER_UNLOCK].done && inf.Stone >= TOWER_STONE_COST) {
        want = BUILDING_ARROWTOWER;                       // 箭塔贴着初始塔
        if (s_twDR >= 0) { anchorDR = s_twDR; anchorUR = s_twUR; }
        else { anchorDR = s_tcDR + 4; anchorUR = s_tcUR + 4; }
    }
    else if (TYPE_OK(BUILDING_HOME) &&
             countAnyBuilding(inf, BUILDING_HOME) < needHome &&  // 总量封顶
             inf.Human_Num >= inf.Human_MaxNum - 1 && inf.Wood >= 30) {
        want = BUILDING_HOME;                             // 人口将满才建房，达量即停
    }
    else if (TYPE_OK(BUILDING_ARMYCAMP) &&
             countAnyBuilding(inf, BUILDING_ARMYCAMP) == 0 &&
             inf.Wood >= 125 && inf.GameFrame > 600) {
        want = BUILDING_ARMYCAMP;                         // 靶场前置，尽早建
    }
    else if (TYPE_OK(BUILDING_MARKET) &&
             countAnyBuilding(inf, BUILDING_MARKET) == 0 &&
             inf.Wood >= 150) {
        want = BUILDING_MARKET;                           // 升铜器前置1
    }
    else if (TYPE_OK(BUILDING_RANGE) &&
             countDoneBuilding(inf, BUILDING_ARMYCAMP) > 0 &&
             countAnyBuilding(inf, BUILDING_RANGE) == 0 &&
             inf.Wood >= 150) {
        want = BUILDING_RANGE;                            // 前置=兵营已建成
    }
    else if (TYPE_OK(BUILDING_FARM) &&
             countAnyBuilding(inf, BUILDING_MARKET) > 0 &&
             countAnyBuilding(inf, BUILDING_FARM) < farmMax &&
             bushLeft == 0 && inf.Wood >= 75) {
        /* v4.3 问题4：浆果一采空立即修农田（原等"浆果+瞪羚全光+1200帧"
         * 导致过晚）；瞪羚保留给猎人，不纳入触发条件 */
        want = BUILDING_FARM;
        /* v4.3 问题5：农田锚定谷仓但偏移5格成片布置，不再紧贴谷仓螺旋
         * 外扩——避免把谷仓四面围死、村民无法进入存食物 */
        const tagBuilding* gd = nearestBuilding(inf, BUILDING_GRANARY,
                                                blockCenter(s_tcDR),
                                                blockCenter(s_tcUR), true);
        if (gd) { anchorDR = gd->BlockDR + 5; anchorUR = gd->BlockUR + 5; }
        else    { anchorDR = s_tcDR - 5;      anchorUR = s_tcUR - 5; }
    }
    /* 问题11：资源聚集地离基地>10格 -> 就地建存放建筑（谷仓收食物、
     * 仓库收木材），与已有建筑间距≥3格防扎堆；各至多2座 */
    else if (TYPE_OK(BUILDING_GRANARY) &&
             countAnyBuilding(inf, BUILDING_GRANARY) < 2 && inf.Wood >= 100) {
        int adr, aur;
        if (remoteCluster(inf, RESOURCE_BUSH, 4, 10.0 * s_bls,
                          BUILDING_GRANARY, adr, aur)) {
            want = BUILDING_GRANARY;
            anchorDR = adr; anchorUR = aur;
        }
    }
    else if (TYPE_OK(BUILDING_STOCK) &&
             countAnyBuilding(inf, BUILDING_STOCK) < 2 && inf.Wood >= 100) {
        int adr, aur;
        if (remoteCluster(inf, RESOURCE_TREE, 8, 12.0 * s_bls,
                          BUILDING_STOCK, adr, aur)) {
            want = BUILDING_STOCK;
            anchorDR = adr; anchorUR = aur;
        }
    }
    #undef TYPE_OK
    if (want < 0) return;

    /* 3) 螺旋选址：箭塔用带塔间距版本（问题6），远程存放建筑用
     *    带建筑间距版本，其余用普通螺旋就近 */
    int dr, ur;
    if (want == BUILDING_ARROWTOWER) {
        if (!findBuildSpotTower(inf, anchorDR, anchorUR, dr, ur)) return;
    } else if (want == BUILDING_GRANARY || want == BUILDING_STOCK) {
        if (!findBuildSpotGap(inf, want, anchorDR, anchorUR,
                              3.0 * s_bls, dr, ur)) return;
    } else if (!findBuildSpot(inf, want, anchorDR, anchorUR, dr, ur)) return;

    /* 4) 最近的空闲村民去建造 */
    const tagFarmer* builder = NULL;
    double bd = 1e18;
    double cx = blockCenter(dr), cy = blockCenter(ur);
    for (size_t i = 0; i < inf.farmers.size(); ++i) {
        const tagFarmer& f = inf.farmers[i];
        if (f.FarmerSort != FARMERTYPE_FARMER) continue;
        if (f.NowState != HUMAN_STATE_IDLE) continue;
        double d = dist2(f.DR, f.UR, cx, cy);
        if (d < bd) { bd = d; builder = &f; }
    }
    if (!builder) return;

    int id = HumanBuild(builder->SN, want, dr, ur);
    s_pend[slot].id = id;
    s_pend[slot].type = want;
    s_pend[slot].dr = dr;
    s_pend[slot].ur = ur;
    s_pend[slot].frame = inf.GameFrame;
    s_pend[slot].builderSN = builder->SN;
    noteFarmerCmd(builder->SN, id, -1, 'M', inf.GameFrame);
}

/*----------------------------------------------------------------------------
 * 2. 建筑行动：科技 / 造村民 / 练兵 / 升级时代
 *    规则：除"解锁箭塔"外，所有科技仅铜器时代研发；
 *          升级条件一满足立即升铜器。
 *--------------------------------------------------------------------------*/
void UsrAI::manageBuildingActions(const tagInfo& inf)
{
    /* 科技指令结果核查 */
    for (int i = 0; i < R_NUM; ++i) {
        if (s_res[i].id < 0 || s_res[i].done) continue;
        map<int,int>::const_iterator it = inf.ins_ret.find(s_res[i].id);
        if (it != inf.ins_ret.end()) {
            if (it->second == ACTION_SUCCESS) s_res[i].done = true;
            else s_res[i].cdUntil = inf.GameFrame + 600;
            s_res[i].id = -1;
        } else if (inf.GameFrame - s_res[i].frame > 900) {
            s_res[i].id = -1;
            s_res[i].cdUntil = inf.GameFrame + 600;
        }
    }

    /* 升级时代指令结果核查 */
    if (s_ageUpgOrdered && s_ageUpgId >= 0) {
        map<int,int>::const_iterator it = inf.ins_ret.find(s_ageUpgId);
        if (it != inf.ins_ret.end()) {
            if (it->second != ACTION_SUCCESS) {
                s_ageUpgOrdered = false;
                s_ageUpgCdUntil = inf.GameFrame + 600;
            }
            s_ageUpgId = -1;
        } else if (inf.GameFrame - s_ageUpgFrame > 1600) {
            /* 升级耗时60秒(1500帧)：期间无ins_ret属正常，超时才判失败 */
            s_ageUpgOrdered = false;
            s_ageUpgId = -1;
            s_ageUpgCdUntil = inf.GameFrame + 600;
        }
    }

    bool bronze = isBronze(inf);
    bool popOk  = (inf.Human_Num < inf.Human_MaxNum - 0.5);
    int  vTarget = villTarget(inf);         // 三段式 12/20/28

    /* v4.2 关键修复（问题2）：进入铜器当帧立即复位升级锁。
     * 原缺陷：s_ageUpgOrdered 置位后不复位，而造村民条件含
     * !s_ageUpgOrdered，导致升铜器后村民生产永久停止。 */
    if (bronze && s_ageUpgOrdered) {
        s_ageUpgOrdered = false;
        s_ageUpgId = -1;
    }

    /* =====================================================================
     * v4.3 兵力目标与练兵许可
     *   - 箭塔强化科技一下令（id>=0）即解除资源冻结，开始造兵
     *   - 硬性配额门控：棍棒兵<4时兵营只造棍棒兵；弓箭手<2时靶场只造弓箭手
     *   - 两者都达标后才解锁其他单位（阔剑兵、复合弓兵等）
     * ===================================================================== */
    int meleeTarget, archerTarget;
    if (!bronze) {
        meleeTarget = 1; archerTarget = 2;
    } else if (inf.GameFrame < WAVE3_SPAWN) {
        meleeTarget = 6; archerTarget = 6;
    } else {
        meleeTarget = 10; archerTarget = 10;
    }
    /* 箭塔强化已下令即允许造兵（不再等完成） */
    bool towerUpgOrdered = (s_res[R_TOWER_UPG].id >= 0 || s_res[R_TOWER_UPG].done);
    bool mayTrain = bronze || (inf.Meat >= BRONZE_FOOD + 60) || towerUpgOrdered;

    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        const tagBuilding& b = inf.buildings[i];
        if (b.Percent < 100) continue;
        if (b.Project != ACT_NULL && b.Type != BUILDING_ARROWTOWER)
            continue;                        // 忙碌（箭塔Project是攻击目标）

        if (b.Type == BUILDING_GRANARY) {
            /* 解锁箭塔：升级前唯一允许的科技 */
            if (!s_res[R_TOWER_UNLOCK].done && s_res[R_TOWER_UNLOCK].id < 0 &&
                inf.GameFrame >= s_res[R_TOWER_UNLOCK].cdUntil &&
                inf.GameFrame > 100 && inf.Meat >= 50) {
                s_res[R_TOWER_UNLOCK].id =
                    BuildingAction(b.SN, BUILDING_GRANARY_ARROWTOWER);
                s_res[R_TOWER_UNLOCK].frame = inf.GameFrame;
            }
            /* v4.3 问题6：箭塔强化=铜器后第一优先级（120食+50石）。
             * 原缺陷：练兵/造村民持续吃食物，与采石科技抢石头，
             * 120食+50石始终凑不齐。现由练兵/造村民/仓库科技的食物
             * 门槛保证优先攒足（见下方各分支）。 */
            else if (bronze && !s_res[R_TOWER_UPG].done &&
                     s_res[R_TOWER_UPG].id < 0 &&
                     inf.GameFrame >= s_res[R_TOWER_UPG].cdUntil &&
                     inf.Meat >= 120 && inf.Stone >= 50) {
                s_res[R_TOWER_UPG].id =
                    BuildingAction(b.SN, BUILDING_GRANARY_ARROWTOWE_UPGRADE);
                s_res[R_TOWER_UPG].frame = inf.GameFrame;
            }
        }
        else if (b.Type == BUILDING_MARKET) {
            /* v4.2 市场科技链（铜器后），花销优先级：
             *   食物：谷仓强化(120) > 驯养动物(200) > 采石(100)
             *   低优先级项需"高优先级已完成"或"资源够双份"才放行，
             *   避免抢占高优先级科技的资源。 */
            if (bronze && !s_res[R_WOOD].done && s_res[R_WOOD].id < 0 &&
                inf.GameFrame >= s_res[R_WOOD].cdUntil &&
                inf.Meat >= 120 && inf.Wood >= 75) {
                /* 问题2：升铜器后立刻研发伐木科技 */
                s_res[R_WOOD].id = BuildingAction(b.SN, BUILDING_MARKET_WOOD_UPGRADE);
                s_res[R_WOOD].frame = inf.GameFrame;
            }
            else if (bronze && !s_res[R_FARM].done && s_res[R_FARM].id < 0 &&
                     inf.GameFrame >= s_res[R_FARM].cdUntil &&
                     countDoneBuilding(inf, BUILDING_FARM) >= 2 &&   // 问题3触发
                     inf.Meat >= 200 && inf.Wood >= 50 &&
                     (s_res[R_TOWER_UPG].done || inf.Meat >= 320)) {
                s_res[R_FARM].id = BuildingAction(b.SN, BUILDING_MARKET_FARM_UPGRADE);
                s_res[R_FARM].frame = inf.GameFrame;
            }
            else if (bronze && !s_res[R_STONE].done && s_res[R_STONE].id < 0 &&
                     inf.GameFrame >= s_res[R_STONE].cdUntil &&
                     inf.Meat >= 100 && inf.Stone >= 50 &&
                     (s_res[R_TOWER_UPG].done || inf.Stone >= 100) &&
                     (s_res[R_FARM].done || inf.Meat >= 300)) {
                s_res[R_STONE].id = BuildingAction(b.SN, BUILDING_MARKET_STONE_UPGRADE);
                s_res[R_STONE].frame = inf.GameFrame;
            }
            else if (bronze && s_res[R_STONE].done && !s_res[R_GOLD].done &&
                     s_res[R_GOLD].id < 0 &&
                     inf.GameFrame >= s_res[R_GOLD].cdUntil &&
                     inf.Meat >= 120 && inf.Wood >= 100) {
                s_res[R_GOLD].id = BuildingAction(b.SN, BUILDING_MARKET_GOLD_UPGRADE);
                s_res[R_GOLD].frame = inf.GameFrame;
            }
        }
        else if (b.Type == BUILDING_STOCK) {
            /* 仓库：工具使用（近战攻+2），铜器后；
             * v4.3 问题6：箭塔强化未完成时让路（防抢100食） */
            if (bronze && s_res[R_TOWER_UPG].done &&
                !s_res[R_USETOOL].done && s_res[R_USETOOL].id < 0 &&
                inf.GameFrame >= s_res[R_USETOOL].cdUntil &&
                inf.Meat >= 100) {
                s_res[R_USETOOL].id =
                    BuildingAction(b.SN, BUILDING_STOCK_UPGRADE_USETOOL);
                s_res[R_USETOOL].frame = inf.GameFrame;
            }
        }
        else if (b.Type == BUILDING_CENTER) {
            /* 最高优先级：立即升铜器（前置=市场+靶场建成，800食物） */
            if (!bronze && !s_ageUpgOrdered &&
                inf.GameFrame >= s_ageUpgCdUntil && inf.Meat >= BRONZE_FOOD &&
                ((countDoneBuilding(inf, BUILDING_MARKET) > 0 &&
                  countDoneBuilding(inf, BUILDING_RANGE) > 0) ||
                 inf.GameFrame - s_lastUpgradeTry >= 1200)) {
                s_ageUpgId = BuildingAction(b.SN, BUILDING_CENTER_UPGRADE);
                s_ageUpgFrame = inf.GameFrame;
                s_ageUpgOrdered = true;
                s_lastUpgradeTry = inf.GameFrame;
            }
            else if (popOk && !s_ageUpgOrdered) {
                /* v4.3 生产节奏门控：
                 * 阶段A（SAVE_FRAME~箭塔强化下令前）：暂停造村民，
                 *   资源优先攒 120食+50石 供箭塔强化；
                 * 阶段B（箭塔强化已下令后）：恢复造村民至目标数，
                 *   同时兵营/靶场开始造兵；
                 * 其余阶段：按三段式目标正常生产 */
                bool savePhase = (inf.GameFrame >= SAVE_FRAME) &&
                                 !towerUpgOrdered;
                if (!savePhase &&
                    villagerCount(inf) + s_villPending < vTarget &&
                    inf.Meat >= VILL_FOOD_COST) {
                    BuildingAction(b.SN, BUILDING_CENTER_CREATEFARMER);
                    ++s_villPending;
                    s_lastVillOrderFrame = inf.GameFrame;
                }
            }
        }
        /* =====================================================================
         * 兵营造兵（v4.3 硬性配额门控）
         *   - 棍棒兵<4时：只造棍棒兵（不升级阔剑兵）
         *   - 棍棒兵≥4后：才允许升级棍棒兵科技、造阔剑兵
         * ===================================================================== */
        else if (b.Type == BUILDING_ARMYCAMP) {
            int clubs = countClubs(inf);
            /* 升级阔剑兵科技：仅当棍棒兵已达标 */
            if (bronze && clubs >= CLUBS_NEED &&
                !s_res[R_CLUB].done && s_res[R_CLUB].id < 0 &&
                inf.GameFrame >= s_res[R_CLUB].cdUntil && inf.Meat >= 100) {
                s_res[R_CLUB].id =
                    BuildingAction(b.SN, BUILDING_ARMYCAMP_UPGRADE_CLUBMAN);
                s_res[R_CLUB].frame = inf.GameFrame;
            }
            /* 造兵：棍棒兵<4时只造棍棒兵；达标后才允许造其他近战 */
            else if (mayTrain && popOk &&
                     inf.GameFrame - s_trainCdFrame >= 90 &&
                     countMelee(inf) < meleeTarget && inf.Meat >= 50 &&
                     /* 箭塔强化未完成时预留食物 */
                     (towerUpgOrdered || inf.Meat >= 200)) {
                if (clubs < CLUBS_NEED) {
                    /* 配额未满：强制造棍棒兵 */
                    BuildingAction(b.SN, BUILDING_ARMYCAMP_CREATE_CLUBMAN);
                } else {
                    /* 配额已满：优先阔剑兵（若科技已研发），否则棍棒兵 */
                    if (s_res[R_CLUB].done && inf.Meat >= 35 && inf.Gold >= 15)
                        BuildingAction(b.SN, BUILDING_ARMYCAMP_CREATE_BROADSWORD);
                    else
                        BuildingAction(b.SN, BUILDING_ARMYCAMP_CREATE_CLUBMAN);
                }
                s_trainCdFrame = inf.GameFrame;
            }
        }
        /* =====================================================================
         * 靶场造兵（v4.3 硬性配额门控）
         *   - 弓箭手<2时：只造弓箭手
         *   - 弓箭手≥2后：才允许造复合弓兵等其他远程
         * ===================================================================== */
        else if (b.Type == BUILDING_RANGE) {
            int archers = countArchers(inf);
            if (mayTrain && popOk &&
                inf.GameFrame - s_trainCdFrame >= 90 &&
                countArchers(inf) < archerTarget &&
                inf.Meat >= 40 && inf.Wood >= 20 &&
                /* 箭塔强化未完成时预留食物 */
                (towerUpgOrdered || inf.Meat >= 200)) {
                if (archers < ARCHERS_NEED) {
                    /* 配额未满：强制造弓箭手 */
                    BuildingAction(b.SN, BUILDING_RANGE_CREATE_BOWMAN);
                } else {
                    /* 配额已满：可造复合弓兵（铜器后） */
                    if (bronze && inf.Meat >= 40 && inf.Wood >= 20)
                        BuildingAction(b.SN, BUILDING_RANGE_CREATE_COMPOSITE_BOWMAN);
                    else
                        BuildingAction(b.SN, BUILDING_RANGE_CREATE_BOWMAN);
                }
                s_trainCdFrame = inf.GameFrame;
            }
        }
    }
}

/*----------------------------------------------------------------------------
 * 3. 村民管理：逃跑 > 上交 > 配额分工采集 > 反发呆兜底(开视野)
 *--------------------------------------------------------------------------*/
void UsrAI::manageFarmers(const tagInfo& inf)
{
    bool bronze = isBronze(inf);
    double fleeR = 5.0 * s_bls;

    /* v4.2 问题7：一人一田。先统计"有资源但0人采集"的农田，
     * 主循环里空闲村民优先补派到这些田（不会多派：上限1由
     * nearestFoodSN 的 workersOnTarget>=1 保证） */
    vector<int> emptyFarms;
    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        const tagBuilding& b = inf.buildings[i];
        if (b.Type != BUILDING_FARM || b.Percent < 100 || b.Cnt <= 0) continue;
        if (workersOnTarget(inf, b.SN, -1) == 0) emptyFarms.push_back(b.SN);
    }

    for (size_t i = 0; i < inf.farmers.size(); ++i) {
        const tagFarmer& f = inf.farmers[i];
        if (f.FarmerSort != FARMERTYPE_FARMER) continue;

        /* 核对上一条指令的执行结果 */
        {
            int lastId = -1;
            map<int,int>::iterator idIt = s_farmerCmdId.find(f.SN);
            if (idIt != s_farmerCmdId.end()) lastId = idIt->second;
            if (lastId >= 0) {
                map<int,int>::const_iterator r = inf.ins_ret.find(lastId);
                if (r != inf.ins_ret.end()) {
                    if (r->second != ACTION_SUCCESS) {
                        int lt = -1; char lk = 0;
                        map<int,int>::iterator tIt = s_farmerCmdTarget.find(f.SN);
                        if (tIt != s_farmerCmdTarget.end()) lt = tIt->second;
                        map<int,char>::iterator kIt = s_farmerCmdKind.find(f.SN);
                        if (kIt != s_farmerCmdKind.end()) lk = kIt->second;
                        if (lt > 0 && lk != 'M')
                            s_targetBadUntil[lt] = inf.GameFrame + 1200;
                        s_farmerStuck[f.SN] += 1;
                    }
                    s_farmerCmdId[f.SN] = -1;
                }
            }
        }

        /* 1) 保命：敌军5格内向远离方向撤退 */
        const tagArmy* en = nearestEnemy(inf, f.DR, f.UR);
        if (en && dist2(f.DR, f.UR, en->DR, en->UR) < fleeR * fleeR) {
            int last = -1000;
            map<int,int>::iterator lf = s_lastFleeFrame.find(f.SN);
            if (lf != s_lastFleeFrame.end()) last = lf->second;
            if (inf.GameFrame - last >= 25) {
                double ddr = f.DR - en->DR, dur = f.UR - en->UR;
                double len = sqrt(ddr * ddr + dur * dur);
                if (len < 1e-6) { ddr = 1.0; dur = 0.0; len = 1.0; }
                double tx = f.DR + ddr / len * 8.0 * s_bls;
                double ty = f.UR + dur / len * 8.0 * s_bls;
                clampDetail(tx, ty);
                HumanMove(f.SN, tx, ty);
                s_lastFleeFrame[f.SN] = inf.GameFrame;
            }
            continue;
        }

        /* 2) 本帧刚被派去建造的村民跳过 */
        bool isBuilder = false;
        for (int k = 0; k < 2; ++k)
            if (s_pend[k].id >= 0 && s_pend[k].builderSN == f.SN) {
                isBuilder = true;
                break;
            }
        if (isBuilder) continue;
        if (f.NowState != HUMAN_STATE_IDLE) continue;

        /* 3) 指令冷却（12帧） */
        int lastFrame = -999;
        { map<int,int>::iterator it = s_farmerCmdFrame.find(f.SN);
          if (it != s_farmerCmdFrame.end()) lastFrame = it->second; }
        if (inf.GameFrame - lastFrame < 12) continue;

        int lastKind   = 0;
        int lastTarget = -1;
        { map<int,char>::iterator it = s_farmerCmdKind.find(f.SN);
          if (it != s_farmerCmdKind.end()) lastKind = it->second; }
        { map<int,int>::iterator it = s_farmerCmdTarget.find(f.SN);
          if (it != s_farmerCmdTarget.end()) lastTarget = it->second; }

        /* 4) 快速回空闲 = 目标没采成 */
        bool quickReturn = (inf.GameFrame - lastFrame < 300);
        if (quickReturn) {
            if (lastKind == 'G' || lastKind == 'M') s_farmerStuck[f.SN] += 1;
        } else {
            s_farmerStuck[f.SN] = 0;
        }

        /* 5) 卡住3次：随机挪位后重新指派 */
        int stuck = 0;
        { map<int,int>::iterator it = s_farmerStuck.find(f.SN);
          if (it != s_farmerStuck.end()) stuck = it->second; }
        if (stuck >= 3) {
            double ang = ((f.SN * 37 + inf.GameFrame * 11) % 360) * 3.14159265 / 180.0;
            double tx = f.DR + cos(ang) * 4.0 * s_bls;
            double ty = f.UR + sin(ang) * 4.0 * s_bls;
            clampDetail(tx, ty);
            HumanMove(f.SN, tx, ty);
            noteFarmerCmd(f.SN, -1, -1, 'M', inf.GameFrame);
            s_farmerStuck[f.SN] = 0;
            continue;
        }

        /* 6) 手持资源 -> 上交（农田食物交谷仓，其余交仓库，TC兜底） */
        if (f.Resource > 0) {
            int wantType = (f.ResourceSort == HUMAN_GRANARYFOOD)
                           ? BUILDING_GRANARY : BUILDING_STOCK;
            const tagBuilding* depot = nearestBuilding(inf, wantType, f.DR, f.UR, true);
            if (!depot || targetBad(inf, depot->SN))
                depot = nearestBuilding(inf, BUILDING_CENTER, f.DR, f.UR, true);
            if (depot) {
                int id = HumanAction(f.SN, depot->SN);
                noteFarmerCmd(f.SN, id, depot->SN, 'D', inf.GameFrame);
            }
            continue;
        }

        /* 7) 手空 -> 按角色采集；无目标依次兜底，绝不发呆
         *    v4.2 问题7：存在0人采集的农田时优先补派（一人一田） */
        char role = pickRole(inf);
        s_farmerRole[f.SN] = role;
        int exclude = (quickReturn && lastKind == 'G') ? lastTarget : -1;
        if (exclude > 0) s_targetBadUntil[exclude] = inf.GameFrame + 300;

        int sn = -1;
        if (!emptyFarms.empty()) {
            sn = emptyFarms.back();
            emptyFarms.pop_back();
            s_farmerRole[f.SN] = 'F';
        }
        if (sn < 0) sn = resourceForRole(inf, f.DR, f.UR, role, f.SN);
        if (sn < 0 && role != 'W') {                 // 本职无目标 -> 伐木
            sn = resourceForRole(inf, f.DR, f.UR, 'W', f.SN);
            if (sn >= 0) s_farmerRole[f.SN] = 'W';
        }
        if (sn < 0 && role != 'F') {                 // 再试食物
            sn = resourceForRole(inf, f.DR, f.UR, 'F', f.SN);
            if (sn >= 0) s_farmerRole[f.SN] = 'F';
        }
        if (sn < 0 && bronze) {                      // 铜器后可采石/金
            sn = resourceForRole(inf, f.DR, f.UR, 'S', f.SN);
            if (sn < 0) sn = resourceForRole(inf, f.DR, f.UR, 'G', f.SN);
            if (sn >= 0) s_farmerRole[f.SN] = 'S';
        }
        if (sn >= 0) {
            int id = HumanAction(f.SN, sn);
            noteFarmerCmd(f.SN, id, sn, 'G', inf.GameFrame);
            continue;
        }

        /* 8) 终极兜底：去最近的探索边界开视野（顺便找新资源） */
        int fdr = -1, fur = -1;
        double minD = 2.0 * s_bls;
        if (nearestFrontier(inf, f.DR, f.UR, minD * minD, fdr, fur)) {
            double tx = blockCenter(fdr), ty = blockCenter(fur);
            HumanMove(f.SN, tx, ty);
            noteFarmerCmd(f.SN, -1, -1, 'M', inf.GameFrame);
        } else {
            const tagBuilding* tc = nearestBuilding(inf, BUILDING_CENTER,
                                                    f.DR, f.UR, true);
            if (tc && inf.GameFrame - lastFrame >= 120) {
                HumanMove(f.SN, blockCenter(tc->BlockDR),
                          blockCenter(tc->BlockUR));
                noteFarmerCmd(f.SN, -1, -1, 'M', inf.GameFrame);
            }
        }
    }
}

/*----------------------------------------------------------------------------
 * 4. 祭司管理（v4.3 重写）
 *    核心策略：转化是制胜关键，冷却就绪即转化最近敌军；
 *             转化后立刻返回三塔火力交集点（质心）；
 *             箭塔优先集火攻击祭司的敌军。
 *
 *    行为优先级：
 *      1) 转化敌军（冷却就绪，射程12格内；射程外则主动走近到10格）
 *      2) 低血逃命（血<45%且敌<4格）
 *      3) 治疗友军（非庇护期，12格内血<70%）
 *      4) 庇护期/敌近身：回三塔质心
 *      5) 探路：去已探索边界
 *      6) 默认驻守：三塔质心
 *--------------------------------------------------------------------------*/

/* 庇护窗口：波次出生前1500帧 ~ 抵达后2500帧 */
static bool inShelterWindow(int fr)
{
    return (fr >= WAVE1_SPAWN - 1500 && fr <= WAVE1_SPAWN + 2500) ||
           (fr >= WAVE2_SPAWN - 1500 && fr <= WAVE2_SPAWN + 2500) ||
           (fr >= WAVE3_SPAWN - 1500);
}

/* 向目标块移动（冷却 + 仅在空闲时下令，避免重置行进路径） */
bool UsrAI::priestMoveTo(const tagInfo& inf, const tagArmy* p,
                         int tdr, int tur, int cooldown)
{
    if (p->NowState != HUMAN_STATE_IDLE) return false;
    if (inf.GameFrame - s_priestCmdFrame < cooldown) return false;
    double tx = blockCenter(tdr), ty = blockCenter(tur);
    if (dist2(p->DR, p->UR, tx, ty) < 2.5 * s_bls * (2.5 * s_bls)) return false;
    int id = HumanMove(p->SN, tx, ty);
    s_priestCmdFrame = inf.GameFrame;
    s_priestCmdId = id;
    s_priestMoveKey = bkey(tdr, tur);
    return true;
}

/* 向精确坐标移动（用于转化后回质心等需要精确落点的场景） */
bool UsrAI::priestMoveToDetail(const tagInfo& inf, const tagArmy* p,
                               double tx, double ty, int cooldown)
{
    if (p->NowState != HUMAN_STATE_IDLE) return false;
    if (inf.GameFrame - s_priestCmdFrame < cooldown) return false;
    if (dist2(p->DR, p->UR, tx, ty) < 2.5 * s_bls * (2.5 * s_bls)) return false;
    int id = HumanMove(p->SN, tx, ty);
    s_priestCmdFrame = inf.GameFrame;
    s_priestCmdId = id;
    s_priestMoveKey = -1;   // 精确坐标不对应整数块，不记录块key
    return true;
}

/* v4.3：计算所有已建成箭塔的质心（火力交集点）。
 * 祭司驻守/躲避的默认位置 = 质心，确保始终处于最多箭塔的交叉火力下。
 * 若尚无箭塔，fallback 到市镇中心。 */
static void getTowerCentroid(const tagInfo& inf, double& cx, double& cy)
{
    double sumX = 0, sumY = 0;
    int cnt = 0;
    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        const tagBuilding& b = inf.buildings[i];
        if (b.Type != BUILDING_ARROWTOWER || b.Percent < 100) continue;
        sumX += blockCenter(b.BlockDR) + 0.5 * s_bls;   // 2x2塔中心
        sumY += blockCenter(b.BlockUR) + 0.5 * s_bls;
        ++cnt;
    }
    if (cnt > 0) {
        cx = sumX / cnt;
        cy = sumY / cnt;
    } else {
        cx = blockCenter(s_tcDR);
        cy = blockCenter(s_tcUR);
    }
}

/* v4.3：判断祭司是否已在质心附近（≤3.5格），用于避免重复下令 */
static bool priestAtCentroid(const tagInfo& inf, const tagArmy* p)
{
    double cx, cy;
    getTowerCentroid(inf, cx, cy);
    return dist2(p->DR, p->UR, cx, cy) < 3.5 * s_bls * 3.5 * s_bls;
}

/* v4.3 问题2：在箭塔周围找一个可达的空地作为躲避点。
 * 箭塔是2x2建筑，其中心点位于建筑体内部——内核的移动指令不做路径
 * 可达性校验（Core_List.cpp:225 只记录目的地即返回成功），部分地图的
 * 寻路无法停在建筑体内，祭司就会"指令成功但原地不动"。
 * 因此躲避目标必须是塔旁的空地。orient 用于卡住后换方位重试。 */
static bool towerSideSpot(const tagInfo& inf, const tagBuilding& tw,
                          int orient, int& odr, int& our_)
{
    /* 塔(2x2)周围8个方位的候选块（相对塔左上角） */
    static const int offs[][2] = {
        { 2,  0}, {-1,  0}, { 0,  2}, { 0, -1},
        { 2,  2}, {-1,  2}, { 2, -1}, {-1, -1}
    };
    for (int i = 0; i < 8; ++i) {
        int idx = (orient + i) % 8;
        int dr = tw.BlockDR + offs[idx][0];
        int ur = tw.BlockUR + offs[idx][1];
        /* 移动目标只需该块已探索且非海洋/未知地形即可，
         * 不用建造预检（那会要求周围3x3全探索，过严） */
        if (!isExplored(inf, dr, ur)) continue;
        if (inf.theMap) {
            const tagTerrain& t = (*inf.theMap)[dr][ur];
            if (t.height < 0 || t.type == MAPPATTERN_OCEAN) continue;
        }
        /* 与所有建筑不重叠 */
        bool free = true;
        for (size_t j = 0; j < inf.buildings.size() && free; ++j) {
            const tagBuilding& b = inf.buildings[j];
            int bw = bsize(b.Type);
            if (dr < b.BlockDR + bw && b.BlockDR < dr + 1 &&
                ur < b.BlockUR + bw && b.BlockUR < ur + 1)
                free = false;
        }
        if (free) { odr = dr; our_ = ur; return true; }
    }
    return false;
}

void UsrAI::managePriest(const tagInfo& inf)
{
    const tagArmy* p = findPriest(inf);
    if (!p) return;

    /* 0) 核对上一条移动指令：失败 -> 拉黑目标块 */
    if (s_priestCmdId >= 0) {
        map<int,int>::const_iterator r = inf.ins_ret.find(s_priestCmdId);
        if (r != inf.ins_ret.end()) {
            if (r->second != ACTION_SUCCESS && s_priestMoveKey >= 0)
                s_scoutBad[s_priestMoveKey] = inf.GameFrame + 3000;
            s_priestCmdId = -1;
            s_priestMoveKey = -1;
        }
    }

    /* 计算三塔质心（火力交集点）—— 祭司的默认驻守/躲避位置 */
    double centX, centY;
    getTowerCentroid(inf, centX, centY);

    /* 找最近敌军及距离 */
    const tagArmy* en = nearestEnemy(inf, p->DR, p->UR);
    double dEn = en ? sqrt(dist2(p->DR, p->UR, en->DR, en->UR)) : 1e18;

    /* v4.2 掉血检测：60帧内掉过血 = 正被攻击 */
    if (s_lastPriestBlood >= 0 && p->Blood < s_lastPriestBlood)
        s_priestHurtFrame = inf.GameFrame;
    s_lastPriestBlood = p->Blood;
    bool hurtNow = (inf.GameFrame - s_priestHurtFrame < 60);

    /* =====================================================================
     * 1) 转化敌军 —— 最高优先级，冷却就绪即转化
     *    恢复 v4.2 策略：仅在射程内（≤12格）且状态允许时直接转化，
     *    移除"走近"逻辑，避免 HumanMove 打断内核正在进行的转化计时。
     * ===================================================================== */
    if (en && p->ConvertCooldown == 0 &&
        dEn <= PRIEST_CONVERT_DIS * s_bls &&
        inf.GameFrame - s_priestSkillFrame >= 40 &&
        (p->NowState == HUMAN_STATE_IDLE ||
         (p->NowState == HUMAN_STATE_WORKING &&
          (hurtNow || dEn < 5.0 * s_bls)))) {
        HumanAction(p->SN, en->SN);
        s_priestSkillFrame = inf.GameFrame;
        return;
    }

    /* =====================================================================
     * 2) 低血逃命：血<45%且敌<4格 -> 向远离敌人方向撤离
     * ===================================================================== */
    if (en && dEn < 4.0 * s_bls && p->Blood * 100 < p->MaxBlood * 45) {
        if (inf.GameFrame - s_priestCmdFrame >= 15) {
            double ddr = p->DR - en->DR, dur = p->UR - en->UR;
            double len = sqrt(ddr * ddr + dur * dur);
            if (len < 1e-6) { ddr = 1.0; dur = 0.0; len = 1.0; }
            double tx = p->DR + ddr / len * 10.0 * s_bls;
            double ty = p->UR + dur / len * 10.0 * s_bls;
            clampDetail(tx, ty);
            HumanMove(p->SN, tx, ty);
            s_priestCmdFrame = inf.GameFrame;
            s_priestCmdId = -1;
            s_priestMoveKey = -1;
        }
        return;
    }

    /* =====================================================================
     * 3) 庇护期/敌近身：回三塔质心（火力交集点）
     *    v4.3 改动：躲避点从"最近单座塔旁"改为"所有箭塔质心"，
     *    确保祭司始终处于最多箭塔的交叉火力保护下。
     * ===================================================================== */
    bool needShelter = inShelterWindow(inf.GameFrame) ||
                       (en && dEn < 20.0 * s_bls);
    bool atCentroid = priestAtCentroid(inf, p);

    if (needShelter && !atCentroid) {
        /* 卡位降级分支：连续3次躲质心失败 -> 不再强求，原地转化或撤离 */
        if (s_shelterTries >= 3) {
            /* a) 射程内有敌且冷却完毕 -> 原地转化 */
            if (en && p->ConvertCooldown == 0 &&
                dEn <= PRIEST_CONVERT_DIS * s_bls &&
                inf.GameFrame - s_priestSkillFrame >= 40) {
                HumanAction(p->SN, en->SN);
                s_priestSkillFrame = inf.GameFrame;
                return;
            }
            /* b) 否则向远离敌人的已探索空点撤离 */
            if (en && p->NowState == HUMAN_STATE_IDLE &&
                inf.GameFrame - s_priestCmdFrame >= 90) {
                double ddr = p->DR - en->DR, dur = p->UR - en->UR;
                double len = sqrt(ddr * ddr + dur * dur);
                if (len < 1e-6) { ddr = 1.0; dur = 0.0; len = 1.0; }
                double tx = p->DR + ddr / len * 8.0 * s_bls;
                double ty = p->UR + dur / len * 8.0 * s_bls;
                clampDetail(tx, ty);
                HumanMove(p->SN, tx, ty);
                s_priestCmdFrame = inf.GameFrame;
                s_priestCmdId = -1;
                s_priestMoveKey = -1;
            }
            return;
        }

        /* 正常分支：向质心移动 */
        if (p->NowState == HUMAN_STATE_IDLE &&
            inf.GameFrame - s_priestCmdFrame >= 30) {
            int id = HumanMove(p->SN, centX, centY);
            s_priestCmdFrame = inf.GameFrame;
            s_priestCmdId = id;
            s_priestMoveKey = -1;
            /* 记录快照，用于卡位检测 */
            s_shelterSnapDR = p->DR;
            s_shelterSnapUR = p->UR;
            s_shelterMoveFrame = inf.GameFrame;
        }

        /* 卡位检测：上次下令300帧后位移<0.8格 -> 计一次失败 */
        if (s_shelterMoveFrame > 0 &&
            inf.GameFrame - s_shelterMoveFrame >= 300) {
            double lim = 0.8 * s_bls;
            if (dist2(p->DR, p->UR, s_shelterSnapDR, s_shelterSnapUR) <
                lim * lim) {
                ++s_shelterTries;
            }
            s_shelterMoveFrame = 0;
        }
        return;
    }
    if (!needShelter) s_shelterTries = 0;   // 非庇护期复位失败计数
    if (atCentroid) s_shelterTries = 0;     // 已到质心，清零

    /* =====================================================================
     * 4) 治疗友军：12格内血量比例最低且<70%的友方单位
     *    庇护期跳过治疗，防止祭司被钉在塔下不转化
     * ===================================================================== */
    if (!needShelter && p->NowState == HUMAN_STATE_IDLE &&
        inf.GameFrame - s_priestSkillFrame >= 40) {
        int healSN = -1;
        double worst = 0.70;
        double hr = 12.0 * s_bls;
        for (size_t i = 0; i < inf.armies.size(); ++i) {
            const tagArmy& a = inf.armies[i];
            if (a.Sort == AT_PRIEST || a.MaxBlood <= 0) continue;
            if (dist2(p->DR, p->UR, a.DR, a.UR) > hr * hr) continue;
            double ratio = (double)a.Blood / a.MaxBlood;
            if (ratio < worst) { worst = ratio; healSN = a.SN; }
        }
        for (size_t i = 0; i < inf.farmers.size(); ++i) {
            const tagFarmer& fm = inf.farmers[i];
            if (fm.MaxBlood <= 0) continue;
            if (dist2(p->DR, p->UR, fm.DR, fm.UR) > hr * hr) continue;
            double ratio = (double)fm.Blood / fm.MaxBlood;
            if (ratio < worst) { worst = ratio; healSN = fm.SN; }
        }
        if (healSN >= 0) {
            HumanAction(p->SN, healSN);
            s_priestSkillFrame = inf.GameFrame;
            return;
        }
    }

    /* =====================================================================
     * 5) 探路：只去已探索边界（前线）；无位移 -> 拉黑换点
     * ===================================================================== */
    {
        /* 位移快照检测：500帧内位移<0.8格 -> 目标不可达 */
        if (s_priestMoveKey >= 0 &&
            inf.GameFrame - s_priestSnapFrame >= 500) {
            if (s_priestSnapKey == s_priestMoveKey && s_priestSnapFrame > 0) {
                double lim = 0.8 * s_bls;
                if (dist2(p->DR, p->UR, s_priestSnapDR, s_priestSnapUR) <
                    lim * lim) {
                    s_scoutBad[s_priestMoveKey] = inf.GameFrame + 3000;
                    s_priestMoveKey = -1;
                }
            }
            s_priestSnapDR = p->DR;
            s_priestSnapUR = p->UR;
            s_priestSnapFrame = inf.GameFrame;
            s_priestSnapKey = s_priestMoveKey;
        }
        /* 已在行进中则不打断 */
        if (p->NowState == HUMAN_STATE_WALKING) return;

        int fdr = -1, fur = -1;
        double minD = 3.0 * s_bls;
        if (nearestFrontier(inf, p->DR, p->UR, minD * minD, fdr, fur)) {
            priestMoveTo(inf, p, fdr, fur, 60);
            return;
        }
    }

    /* =====================================================================
     * 6) 默认驻守：三塔质心（火力交集点）
     * ===================================================================== */
    if (!priestAtCentroid(inf, p) && p->NowState == HUMAN_STATE_IDLE &&
        inf.GameFrame - s_priestCmdFrame >= 120) {
        int id = HumanMove(p->SN, centX, centY);
        s_priestCmdFrame = inf.GameFrame;
        s_priestCmdId = id;
        s_priestMoveKey = -1;
    }
}

/*----------------------------------------------------------------------------
 * 5. 箭塔管理（v4.3 重写）
 *    索敌优先级：
 *      1) 正在攻击祭司的敌军（WorkObjectSN == 祭司SN）—— 最高优先级
 *      2) 射程内最近的敌军 —— 默认 fallback
 *    目的：保护祭司，让箭塔成为祭司的贴身护卫。
 *--------------------------------------------------------------------------*/
void UsrAI::manageTowers(const tagInfo& inf)
{
    /* 先找祭司，用于判定"攻击祭司的敌军" */
    const tagArmy* priest = findPriest(inf);
    int priestSN = priest ? priest->SN : -1;

    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        const tagBuilding& b = inf.buildings[i];
        if (b.Type != BUILDING_ARROWTOWER || b.Percent < 100) continue;
        if (b.Project >= 0) continue;   // 已有攻击目标

        int last = -1000;
        map<int,int>::iterator it = s_towerCmdFrame.find(b.SN);
        if (it != s_towerCmdFrame.end()) last = it->second;
        if (inf.GameFrame - last < 10) continue;

        double tx = blockCenter(b.BlockDR), ty = blockCenter(b.BlockUR);
        double range = 8.0 * s_bls;     // 射程7格（强化后8格），留余量
        double range2 = range * range;

        /* 优先级1：找正在攻击祭司的敌军 */
        const tagArmy* target = NULL;
        double bestD = 1e18;
        if (priestSN >= 0) {
            for (size_t j = 0; j < inf.enemy_armies.size(); ++j) {
                const tagArmy& e = inf.enemy_armies[j];
                /* WorkObjectSN 表示该敌军当前锁定的攻击目标 */
                if (e.WorkObjectSN != priestSN) continue;
                double d = dist2(tx, ty, e.DR, e.UR);
                if (d < range2 && d < bestD) {
                    bestD = d;
                    target = &e;
                }
            }
        }

        /* 优先级2：若无攻击祭司的敌军在射程内，则攻击最近的敌军 */
        if (!target) {
            for (size_t j = 0; j < inf.enemy_armies.size(); ++j) {
                const tagArmy& e = inf.enemy_armies[j];
                double d = dist2(tx, ty, e.DR, e.UR);
                if (d < range2 && d < bestD) {
                    bestD = d;
                    target = &e;
                }
            }
        }

        if (target) {
            HumanAction(b.SN, target->SN);
            s_towerCmdFrame[b.SN] = inf.GameFrame;
        }
    }
}

/*----------------------------------------------------------------------------
 * 6. 军队管理：护祭司优先；敌军进入基地警戒圈(28格)才出击；
 *    无敌情时集结在塔簇附近
 *--------------------------------------------------------------------------*/
void UsrAI::manageArmies(const tagInfo& inf)
{
    if (s_tcDR < 0) return;
    double gx, gy;
    if (s_twDR >= 0) { gx = blockCenter(s_twDR + 1); gy = blockCenter(s_twUR + 1); }
    else { gx = blockCenter(s_tcDR + 4); gy = blockCenter(s_tcUR + 4); }
    double d = 3.0 * s_bls;
    double tcx = blockCenter(s_tcDR), tcy = blockCenter(s_tcUR);
    double engageR = 28.0 * s_bls;

    /* 护祭司：锁定进入祭司20格内的敌军 */
    const tagArmy* priest = findPriest(inf);
    const tagArmy* threat = NULL;
    if (priest) {
        threat = nearestEnemy(inf, priest->DR, priest->UR);
        if (threat) {
            double pd = 20.0 * s_bls;
            if (dist2(priest->DR, priest->UR, threat->DR, threat->UR) > pd * pd)
                threat = NULL;
        }
    }

    for (size_t i = 0; i < inf.armies.size(); ++i) {
        const tagArmy& a = inf.armies[i];
        if (a.Sort == AT_PRIEST) continue;

        if (!inf.enemy_armies.empty()) {
            if (a.NowState != HUMAN_STATE_IDLE &&
                a.NowState != HUMAN_STATE_WALKING) continue;

            int last = -1000;
            map<int,int>::iterator it = s_armyCmdFrame.find(a.SN);
            if (it != s_armyCmdFrame.end()) last = it->second;
            if (inf.GameFrame - last < 15) continue;

            const tagArmy* target = threat;
            if (!target) {
                const tagArmy* best = NULL;
                double bd = 1e18;
                for (size_t j = 0; j < inf.enemy_armies.size(); ++j) {
                    const tagArmy& e = inf.enemy_armies[j];
                    if (dist2(tcx, tcy, e.DR, e.UR) > engageR * engageR) continue;
                    double dd = dist2(a.DR, a.UR, e.DR, e.UR);
                    if (dd < bd) { bd = dd; best = &e; }
                }
                target = best;
            }
            if (target) {
                HumanAction(a.SN, target->SN);
                s_armyCmdFrame[a.SN] = inf.GameFrame;
            }
        }
        else if (a.NowState == HUMAN_STATE_IDLE &&
                 dist2(a.DR, a.UR, gx, gy) > d * d) {
            int last = -1000;
            map<int,int>::iterator it = s_armyCmdFrame.find(a.SN);
            if (it != s_armyCmdFrame.end()) last = it->second;
            if (inf.GameFrame - last >= 30) {
                HumanMove(a.SN, gx, gy);
                s_armyCmdFrame[a.SN] = inf.GameFrame;
            }
        }
    }
}

/*============================================================================
 * AI 主入口：每帧调用
 *==========================================================================*/
void UsrAI::processData()
{
    info = getInfo();
    const tagInfo& inf = info;

    /* 首帧初始化 */
    if (s_tcDR < 0) {
        s_bls = BLOCKSIDELENGTH;
        for (int i = 0; i < R_NUM; ++i) {
            s_res[i].id = -1;
            s_res[i].frame = 0;
            s_res[i].cdUntil = 0;
            s_res[i].done = false;
        }
        for (int k = 0; k < 2; ++k) {
            s_pend[k].id = -1;
            s_pend[k].type = -1;
            s_pend[k].dr = -1;
            s_pend[k].ur = -1;
            s_pend[k].frame = 0;
            s_pend[k].builderSN = -1;
        }
        s_ageUpgId = -1;
        s_ageUpgOrdered = false;
        s_priestCmdId = -1;
        s_priestMoveKey = -1;
        s_priestCmdFrame = -999;
        s_trainCdFrame = 0;
        s_villPending = 0;

        const tagBuilding* tc = NULL;
        const tagBuilding* tw0 = NULL;
        for (size_t i = 0; i < inf.buildings.size(); ++i) {
            if (inf.buildings[i].Type == BUILDING_CENTER && !tc)
                tc = &inf.buildings[i];
            if (inf.buildings[i].Type == BUILDING_ARROWTOWER && !tw0)
                tw0 = &inf.buildings[i];
        }
        if (tc)  { s_tcDR = tc->BlockDR;  s_tcUR = tc->BlockUR; }
        else     { s_tcDR = 22; s_tcUR = 20; }
        if (tw0) { s_twDR = tw0->BlockDR; s_twUR = tw0->BlockUR; }
        s_lastFarmerCnt = villagerCount(inf);
    }

    /* 更新探索集合与前线 */
    updateExplored(inf);

    /* 村民在生产队列的出队核算（超时则清空，防止指令被拒后卡死） */
    int nowFarmers = villagerCount(inf);
    if (nowFarmers > s_lastFarmerCnt) {
        s_villPending -= (nowFarmers - s_lastFarmerCnt);
        if (s_villPending < 0) s_villPending = 0;
    }
    if (s_villPending > 0 && inf.GameFrame - s_lastVillOrderFrame > 1200)
        s_villPending = 0;
    s_lastFarmerCnt = nowFarmers;

    /* 周期性清理阵亡村民的状态 */
    if (inf.GameFrame % 600 == 0) cleanFarmerMaps(inf);

    manageBuild(inf);           // 建造（螺旋选址+坐标拉黑）
    manageBuildingActions(inf); // 研发/造村民/练兵/升级时代
    manageFarmers(inf);         // 村民（分工采集+反发呆）
    managePriest(inf);          // 祭司（转换/治疗/探路）
    manageTowers(inf);          // 箭塔
    manageArmies(inf);          // 军队

    /* 周期性状态输出（每600帧=24秒） */
    if (inf.GameFrame % 600 == 0) {
        const tagArmy* priest = findPriest(inf);
        DebugText(QString(
            "[AIv4] f=%1 meat=%2 wood=%3 stone=%4 gold=%5 pop=%6/%7 civ=%8 "
            "vill=%9 army=%10 tw=%11 farm=%12 explored=%13 upg=%14 priestHp=%15")
            .arg(inf.GameFrame).arg(inf.Meat).arg(inf.Wood).arg(inf.Stone)
            .arg(inf.Gold)
            .arg(inf.Human_Num).arg(inf.Human_MaxNum)
            .arg(inf.civilizationStage)
            .arg(nowFarmers)
            .arg(armyCountNonPriest(inf))
            .arg(countAnyBuilding(inf, BUILDING_ARROWTOWER))
            .arg(countAnyBuilding(inf, BUILDING_FARM))
            .arg((int)s_explored.size())
            .arg(s_ageUpgOrdered ? 1 : 0)
            .arg(priest ? priest->Blood : 0));
    }
}
