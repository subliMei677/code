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
 * AI v6.0 —— 岗位序列 + 建造流水线 + 三兵种满人口版
 *
 * 本版按需求方给出的策略重写，与旧版（v5.x）冲突处一律以新策略为准：
 *   - 取消"第一波前村民12人上限"，改为按岗位序列持续生产
 *   - 箭塔目标 4座 -> 2座（初始塔 + 新建1座）
 *   - 取消"第三波前禁止造兵"，改为三种兵一路造到人口上限
 *   - 只造 复合弓手 / 侦察骑兵 / 方阵兵 三种兵，兵营不再造兵
 *
 * 引擎事实（已在 Development.cpp / Building.cpp / config.h 核对）：
 *   - 我方初始即工具时代；升铜器 = 800食物，前置需市场+靶场建成
 *   - 学院 = 铜器 + 马厩；复合弓手 = 铜器 + 靶场 + 复合弓科技
 *     方阵兵 = 铜器 + 学院；侦察骑兵 = 工具时代即可（100食物）
 *   - 靶场/马厩前置都是兵营；农田前置是市场；箭塔前置是谷仓"解锁箭塔"科技
 *   - 仓库收 木/石/金/STOCKFOOD(肉)；谷仓只收 GRANARYFOOD(农田食物)
 *     浆果与瞪羚肉都是 STOCKFOOD -> 交仓库；农田食物 -> 交谷仓
 *   - 敌方三波：6000 / 13500 / 21000 帧（enemyai.cpp）
 *   - 7g 起 HumanMove 可前往未探索坐标并自动寻路（祭司探路据此简化）
 *==========================================================================*/
#include <map>
#include <vector>
#include <cmath>

tagInfo info;

/*----------------------------------------------------------------------------
 * 常量
 *--------------------------------------------------------------------------*/
static const int WAVE1_SPAWN = 6000;
static const int WAVE2_SPAWN = 13500;
static const int WAVE3_SPAWN = 21000;

static const int BRONZE_FOOD      = 800;   // 升铜器花费
static const int TOWER_STONE_COST = 150;   // 单座箭塔石料
static const int VILL_FOOD_COST   = 50;    // 造村民花费
static const int TOWER_TARGET     = 2;     // v6.0：箭塔总数改为2（含初始塔）
static const int HOME_TARGET      = 12;    // 房屋总数目标
static const int STONE_ENOUGH     = 250;   // 采石"足够"阈值（2塔+解锁科技+余量）
static const int FARM_TOTAL       = 10;    // 农田总数：5块围谷仓 + 5块围市政中心
static const int FARM_PER_ANCHOR  = 5;     // 每个锚点旁的农田数
static const int VILL_TOTAL       = 19;    // 村民总数上限：初始8 + 新生产11
static const int PRIEST_CONVERT_DIS = 12;  // 祭司转化射程

/* 岗位序列配额（按生产顺序分配）
 * v6.3：新村民共 11 个 = 2浆果 + 6猎瞪羚 + 3伐木，之后停产（只有死亡才补员）
 *       第 9~11 个由"采金"改为"伐木"（解决采木过慢）；
 *       采金改为：升铜器后从伐木工里抽调 3 人（加上猎人转的 3 人，共 6 人） */
static const int SEQ_BERRY_NUM = 2;        // 产出第1~2个 -> 浆果
static const int SEQ_HUNT_NUM  = 6;        // 产出第3~8个 -> 猎瞪羚
static const int SEQ_WOOD_NUM  = 3;        // 产出第9~11个 -> 伐木
static const int FARM_WORKER_NUM = 10;     // 农田工目标人数
static const int MAX_WOOD_WORKER = 10;     // 伐木工人数上限
static const int HUNT_TO_GOLD   = 3;       // 猎人采完肉后转采金的人数（其余转伐木）
static const int AGEUP_GOLD_NUM = 3;       // 升铜器后从伐木工抽调去采金的人数
static const int FARM_WOOD_MIN = 100;      // 开始建农田的木材门槛（农田造价75木）
static const int GOLD_WORKER_TARGET = HUNT_TO_GOLD + AGEUP_GOLD_NUM; // 采金工总目标=6
static const int GAZELLE_GIVEUP_FRAME = 18000; // v6.6：超过此帧还没探到瞪羚，猎人放弃等待、正常转岗

/*----------------------------------------------------------------------------
 * 基地锚点（首帧读取实际位置，兼容随机地图随机旋转）
 *--------------------------------------------------------------------------*/
static double s_bls = 35.777;              // 块边长
static int s_tcDR = -1, s_tcUR = -1;       // 市镇中心
static int s_twDR = -1, s_twUR = -1;       // 初始箭塔
static int s_homeDR = -1, s_homeUR = -1;   // 初始房屋（新房屋建在它旁边）
static int s_stockDR = -1, s_stockUR = -1; // 初始仓库（伐木点选它附近）
static int s_granaryDR = -1, s_granaryUR = -1;  // 初始谷仓（农田锚点之一）

/*----------------------------------------------------------------------------
 * 探索集合与探索边界
 *--------------------------------------------------------------------------*/
static set<int> s_explored;                // key = DR*1000+UR
static vector<pair<int,int> > s_frontier;  // 已探索且紧邻未探索的块
static int s_frontierFrame = -9999;

/*----------------------------------------------------------------------------
 * v6.0 村民岗位系统
 *   每个村民固定一个岗位，岗位决定他采什么/干什么。
 *   岗位字符：'B'浆果 'W'木 'S'石 'G'金 'H'猎瞪羚 'C'建造 'F'农田
 *--------------------------------------------------------------------------*/
static map<int,char> s_job;                // 村民SN -> 岗位
static map<int,int>  s_jobOrder;           // 村民SN -> 分配序号（调试用）
static int s_seqIdx = 0;                   // 已分配岗位的新村民数（产出序列计数）
static bool s_initJobsDone = false;        // 初始岗位分配是否已完成
static int s_builderSN = -1;               // 专职建造工的SN（全程只有1个）
static bool s_builderRetired = false;      // 建造工是否已完工转岗采金

/* 岗位人数统计用的缓存（每帧重算） */
static int s_cntB = 0, s_cntW = 0, s_cntS = 0, s_cntG = 0;
static int s_cntH = 0, s_cntF = 0, s_cntC = 0;

/*----------------------------------------------------------------------------
 * v6.0 建造流水线
 *   房屋x2 -> 箭塔x1 -> 市场 -> 兵营 -> 靶场 -> 马厩 -> 学院 -> 补房到12
 *   人口将满（距上限<=4）时插队建房屋
 *--------------------------------------------------------------------------*/
enum BuildStep {
    STEP_HOME2 = 0,     // 开局2座房屋
    STEP_MARKET,        // 市场（2房建好后立刻建）
    STEP_TOWER,         // 箭塔（市场之后，需谷仓"解锁箭塔"科技）
    STEP_HOME2B,        // 再2座房屋
    STEP_ARMYCAMP,      // 兵营
    STEP_RANGE,         // 靶场
    STEP_STABLE,        // 马厩（v6.6：靶场之后直接建马厩，不再插 2 房）
    STEP_COLLAGE,       // 学院（需铜器）
    STEP_HOMEDEMAND,    // v6.5：学院之后改为"按需建房"（保证4人口预留）
    STEP_DONE           // 流水线结束
};
static int s_buildStep = STEP_HOME2;
static int s_homeBuiltByMe = 0;            // 流水线已下单的房屋数（v6.6 共4座，其余按需补到12）

struct PendBuild { int id; int type; int dr; int ur; int frame; int builderSN; };
static PendBuild s_pend;                   // v6.0：只有1个建造工，单槽位即可
static set<int> s_badSpot;                 // 永久拉黑的建造块
static map<int,int> s_spotSkipUntil;       // 临时跳过的建造块
static map<int,int> s_buildTypeCdUntil;    // 建筑类型失败冷却

/* 两处定点仓库（各只建一次） */
static bool s_stockGazelleDone = false;    // 瞪羚群旁仓库已建/在建
static bool s_stockGoldDone = false;       // 金矿旁仓库已建/在建

/* 农田锚点分配：前5块围谷仓，后5块围市政中心 */
static int s_farmIdx = 0;

/*----------------------------------------------------------------------------
 * 科技状态机（一次性科技，经 ins_ret 确认）
 *--------------------------------------------------------------------------*/
struct ResearchState { int id; int frame; int cdUntil; bool done; };
enum { R_TOWER_UNLOCK = 0,   // 谷仓：解锁箭塔（50食）——建塔前置
       R_TOWER_UPG,          // 谷仓：箭塔强化（铜器，120食50石）
       R_WOOD,               // 市场：木材加工（市场建成即研）
       R_COMPOSITE,          // 靶场：复合弓科技（靶场建成即研）
       R_FARM,               // 市场：驯养动物（农田>=2后研）
       R_STONE,              // 市场：石矿开采
       R_GOLD,               // 市场：金矿开采
       R_USETOOL,            // 仓库：工具使用
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
 * 村民生产与指令记录
 *--------------------------------------------------------------------------*/
static int s_villPending = 0;
static int s_lastFarmerCnt = 0;
static int s_lastVillOrderFrame = -9999;

static map<int,int>  s_farmerCmdFrame;
static map<int,int>  s_farmerCmdId;
static map<int,int>  s_farmerCmdTarget;
static map<int,char> s_farmerCmdKind;      // 'G'采集 'D'上交 'M'移动 'A'攻击
static map<int,int>  s_farmerStuck;
static map<int,int>  s_targetBadUntil;

/* 猎瞪羚：给每个猎人锁定一只不同的瞪羚，先把整组打死再采肉 */
static map<int,int> s_huntTarget;          // 村民SN -> 锁定的瞪羚SN

/* 伐木（v6.3 一树一人）：每个伐木工长期负责一棵树，避免多人挤同一棵树 */
static map<int,int> s_woodTree;            // 伐木工SN -> 负责的树SN

/*----------------------------------------------------------------------------
 * 祭司状态
 *--------------------------------------------------------------------------*/
static int s_priestCmdFrame = -999;
static int s_priestCmdId = -1;
static int s_priestMoveKey = -1;
static map<int,int> s_scoutBad;
static double s_priestSnapDR = 0, s_priestSnapUR = 0;
static int s_lastPriestBlood = -1;
static int s_priestHurtFrame = -9999;
static int s_priestSnapFrame = 0;
static int s_priestSnapKey = -1;
static int s_priestSkillFrame = -999;
static int s_shelterTries = 0;
static int s_shelterMoveFrame = -9999;
static double s_shelterSnapDR = 0, s_shelterSnapUR = 0;

/* v6.0 祭司探路：探明金矿后回塔下驻守
 * v6.5：探路目标扩展为"金矿 + 瞪羚"都探到才收工
 *       （否则金矿离基地近时会提前收工，导致部分地图一直没探到瞪羚、
 *         瞪羚群旁仓库也就建不出来） */
static bool s_goldFound = false;           // 是否已探明金矿
static bool s_gazelleFound = false;        // 是否已探明瞪羚群
static int  s_scoutStartFrame = -1;        // 开始探路的帧（超时兜底用）

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

/* 有效农田数：已建成且还有食物(Cnt>0)的农田。
 * 采光的农田内核会自动回收（Core.cpp 里 !is_Surplus() 即删除），
 * 这里再兜一层：万一还没被回收，也不算进目标数，以便及时补建。 */
static int countLiveFarms(const tagInfo& inf)
{
    int n = 0;
    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        const tagBuilding& b = inf.buildings[i];
        if (b.Type != BUILDING_FARM) continue;
        if (b.Percent >= 100 && b.Cnt <= 0) continue;   // 已采光，待回收
        ++n;
    }
    return n;
}

static int armyCountNonPriest(const tagInfo& inf)
{
    int n = 0;
    for (size_t i = 0; i < inf.armies.size(); ++i)
        if (inf.armies[i].Sort != AT_PRIEST) ++n;
    return n;
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

static int villagerCount(const tagInfo& inf)
{
    int n = 0;
    for (size_t i = 0; i < inf.farmers.size(); ++i)
        if (inf.farmers[i].FarmerSort == FARMERTYPE_FARMER) ++n;
    return n;
}

/*----------------------------------------------------------------------------
 * 探索集合维护
 *--------------------------------------------------------------------------*/
static void seedExploredFromMap(const tagInfo& inf);
static bool s_seedDone = false;

static void updateExplored(const tagInfo& inf)
{
    size_t before = s_explored.size();
    for (size_t i = 0; i < inf.exploredUpdate.size(); ++i)
        s_explored.insert(bkey(inf.exploredUpdate[i].x,
                               inf.exploredUpdate[i].y));
    /* 首帧从 theMap 补全初始已探索区域（内核不会经 exploredUpdate 下发） */
    if (!s_seedDone && inf.theMap) {
        seedExploredFromMap(inf);
        s_seedDone = true;
    }
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

/* 探索判定：增量集合 + theMap 类型非 UNKNOWN 双口径 */
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
    /* 房屋/箭塔/船坞 2x2，其余 3x3 */
    if (type == BUILDING_HOME || type == BUILDING_ARROWTOWER ||
        type == BUILDING_DOCK)
        return 2;
    return 3;
}

/* 占地校验：边界 + 整块已探索(外扩1圈) + 平地无海 */
static bool areaBuildable(const tagInfo& inf, int dr, int ur, int w)
{
    if (dr < 1 || ur < 1 || dr + w > MAP_L - 1 || ur + w > MAP_U - 1)
        return false;
    if (!areaExplored(inf, dr - 1, ur - 1, w + 2)) return false;
    if (inf.theMap == NULL) return true;
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

/* 占地无重叠：建筑(含1格间隔防堵路) / 在途 / 静态资源 / 动物 */
static bool areaFree(const tagInfo& inf, int dr, int ur, int w)
{
    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        const tagBuilding& b = inf.buildings[i];
        int bw = bsize(b.Type);
        /* 与已有建筑间隔至少1格，避免把路堵死 */
        if (dr < b.BlockDR + bw + 1 && b.BlockDR < dr + w + 1 &&
            ur < b.BlockUR + bw + 1 && b.BlockUR < ur + w + 1)
            return false;
    }
    if (s_pend.id >= 0 && s_pend.type >= 0) {
        int bw = bsize(s_pend.type);
        if (dr < s_pend.dr + bw && s_pend.dr < dr + w &&
            ur < s_pend.ur + bw && s_pend.ur < ur + w)
            return false;
    }
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
    /* 动物会走动，也算占地 */
    for (size_t i = 0; i < inf.resources.size(); ++i) {
        const tagResource& r = inf.resources[i];
        if (r.Type != RESOURCE_GAZELLE && r.Type != RESOURCE_ELEPHANT)
            continue;
        if (r.Cnt <= 0) continue;
        if (dr < r.BlockDR + 2 && r.BlockDR < dr + w &&
            ur < r.BlockUR + 2 && r.BlockUR < ur + w)
            return false;
    }
    return true;
}

/* 螺旋搜索第一个合法建造位 */
static bool findBuildSpot(const tagInfo& inf, int type,
                          int adr, int aur, int& odr, int& our_)
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
                odr = dr; our_ = ur;
                return true;
            }
        }
    }
    return false;
}

/* 螺旋搜索 + 距某中心至少 minDist 格（市场要远离市政中心，给农田留位） */
static bool findBuildSpotFar(const tagInfo& inf, int type,
                             int adr, int aur,
                             double cx, double cy, double minDist,
                             int& odr, int& our_)
{
    int w = bsize(type);
    double md2 = minDist * minDist;
    for (int r = 1; r <= 22; ++r) {
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
                double bx = blockCenter(dr) + (w - 1) * 0.5 * s_bls;
                double by = blockCenter(ur) + (w - 1) * 0.5 * s_bls;
                if (dist2(bx, by, cx, cy) < md2) continue;   // 太近，跳过
                odr = dr; our_ = ur;
                return true;
            }
        }
    }
    return false;
}

/* 地图边缘建造：从地图四边向内螺旋搜索合法位，给中心留农田空间 */
static bool findBuildSpotEdge(const tagInfo& inf, int type,
                              int& odr, int& our_)
{
    int w = bsize(type);
    int L = MAP_L, U = MAP_U;
    /* 四边候选起点：上、下、左、右（留3格边距防出界） */
    static const int edgeStarts[4][2] = {
        {3, 3}, {3, U - 4}, {L - 4, 3}, {L - 4, U - 4}
    };
    for (int e = 0; e < 4; ++e) {
        int sx = edgeStarts[e][0], sy = edgeStarts[e][1];
        for (int r = 0; r <= 16; ++r) {
            for (int dx = -r; dx <= r; ++dx) {
                for (int dy = -r; dy <= r; ++dy) {
                    int mx = abs(dx), my = abs(dy);
                    if ((mx > my ? mx : my) != r) continue;
                    int dr = sx + dx, ur = sy + dy;
                    if (dr < 1 || ur < 1 || dr + w > L - 1 || ur + w > U - 1)
                        continue;
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
    }
    return false;
}

/* 地图边缘建造 + 距谷仓至少 minDist 格（兵营/靶场防堵路） */
static bool findBuildSpotEdgeFar(const tagInfo& inf, int type,
                                 double minDist,
                                 int& odr, int& our_)
{
    int w = bsize(type);
    int L = MAP_L, U = MAP_U;
    double md2 = minDist * minDist;
    /* 谷仓位置 */
    double gx = -1, gy = -1;
    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        if (inf.buildings[i].Type == BUILDING_GRANARY) {
            gx = blockCenter(inf.buildings[i].BlockDR);
            gy = blockCenter(inf.buildings[i].BlockUR);
            break;
        }
    }
    static const int edgeStarts[4][2] = {
        {3, 3}, {3, U - 4}, {L - 4, 3}, {L - 4, U - 4}
    };
    for (int e = 0; e < 4; ++e) {
        int sx = edgeStarts[e][0], sy = edgeStarts[e][1];
        for (int r = 0; r <= 16; ++r) {
            for (int dx = -r; dx <= r; ++dx) {
                for (int dy = -r; dy <= r; ++dy) {
                    int mx = abs(dx), my = abs(dy);
                    if ((mx > my ? mx : my) != r) continue;
                    int dr = sx + dx, ur = sy + dy;
                    if (dr < 1 || ur < 1 || dr + w > L - 1 || ur + w > U - 1)
                        continue;
                    int key = bkey(dr, ur);
                    if (s_badSpot.count(key)) continue;
                    map<int,int>::const_iterator sk = s_spotSkipUntil.find(key);
                    if (sk != s_spotSkipUntil.end() && inf.GameFrame < sk->second)
                        continue;
                    if (!areaBuildable(inf, dr, ur, w)) continue;
                    if (!areaFree(inf, dr, ur, w)) continue;
                    /* 距谷仓检查 */
                    if (gx >= 0) {
                        double bx = blockCenter(dr) + (w - 1) * 0.5 * s_bls;
                        double by = blockCenter(ur) + (w - 1) * 0.5 * s_bls;
                        if (dist2(bx, by, gx, gy) < md2) continue;
                    }
                    odr = dr; our_ = ur;
                    return true;
                }
            }
        }
    }
    return false;
}

/* 箭塔专用：塔间距>=4格（防投石车溅射一次打两塔） */
static bool findBuildSpotTower(const tagInfo& inf,
                               int adr, int aur, int& odr, int& our_)
{
    const int w = bsize(BUILDING_ARROWTOWER);
    const double minGap = 4.0 * s_bls;
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
                double cx = blockCenter(dr) + 0.5 * s_bls;
                double cy = blockCenter(ur) + 0.5 * s_bls;
                bool gapOk = true;
                for (size_t i = 0; i < inf.buildings.size() && gapOk; ++i) {
                    const tagBuilding& b = inf.buildings[i];
                    if (b.Type != BUILDING_ARROWTOWER) continue;
                    double bx = blockCenter(b.BlockDR) + 0.5 * s_bls;
                    double by = blockCenter(b.BlockUR) + 0.5 * s_bls;
                    if (dist2(cx, cy, bx, by) < minGap * minGap) gapOk = false;
                }
                if (!gapOk) continue;
                odr = dr; our_ = ur;
                return true;
            }
        }
    }
    return false;
}

/* 农田专用：田与田之间至少隔1格（3x3田 => 左上角相距>=4） */
static bool findBuildSpotFarm(const tagInfo& inf,
                              int adr, int aur, int& odr, int& our_)
{
    const int w = 3;
    for (int r = 1; r <= 14; ++r) {
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
                /* 与已有/在途农田至少隔1格 */
                bool gapOk = true;
                for (size_t i = 0; i < inf.buildings.size() && gapOk; ++i) {
                    const tagBuilding& b = inf.buildings[i];
                    if (b.Type != BUILDING_FARM) continue;
                    bool sepDR = (dr + w < b.BlockDR) || (b.BlockDR + w < dr);
                    bool sepUR = (ur + w < b.BlockUR) || (b.BlockUR + w < ur);
                    if (!sepDR && !sepUR) gapOk = false;
                }
                if (gapOk && s_pend.id >= 0 && s_pend.type == BUILDING_FARM) {
                    bool sepDR = (dr + w < s_pend.dr) || (s_pend.dr + w < dr);
                    bool sepUR = (ur + w < s_pend.ur) || (s_pend.ur + w < ur);
                    if (!sepDR && !sepUR) gapOk = false;
                }
                if (!gapOk) continue;
                odr = dr; our_ = ur;
                return true;
            }
        }
    }
    return false;
}

/* 资源旁建仓库：与已有仓库>=7格，避免重复建仓 */
static bool hasStoreNearby(const tagInfo& inf, int type, double dr, double ur,
                           double gap)
{
    double gap2 = gap * gap;
    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        const tagBuilding& b = inf.buildings[i];
        if ((int)b.Type != type) continue;
        if (dist2(dr, ur, blockCenter(b.BlockDR), blockCenter(b.BlockUR)) < gap2)
            return true;
    }
    if (s_pend.id >= 0 && s_pend.type == type) {
        if (dist2(dr, ur, blockCenter(s_pend.dr), blockCenter(s_pend.ur)) < gap2)
            return true;
    }
    return false;
}

/*----------------------------------------------------------------------------
 * v6.0 岗位系统
 *   每帧统计各岗位在职人数，给无岗位村民按序列分配：
 *     产出第1~2个 -> 浆果('B')；第3~8个 -> 猎瞪羚('H')；
 *     第9~14个 -> 采金('G')；第15个起 -> 农田('F')，农田满10人后停产。
 *   初始8人的固定分工在 assignInitialJobs 里处理。
 *--------------------------------------------------------------------------*/

static char jobOf(int sn)
{
    map<int,char>::const_iterator it = s_job.find(sn);
    return (it != s_job.end()) ? it->second : 0;
}

/* 统计各岗位人数（每帧开头调用一次） */
static void countJobs(const tagInfo& inf)
{
    s_cntB = s_cntW = s_cntS = s_cntG = 0;
    s_cntH = s_cntF = s_cntC = 0;
    for (size_t i = 0; i < inf.farmers.size(); ++i) {
        if (inf.farmers[i].FarmerSort != FARMERTYPE_FARMER) continue;
        char j = jobOf(inf.farmers[i].SN);
        switch (j) {
        case 'B': ++s_cntB; break;
        case 'W': ++s_cntW; break;
        case 'S': ++s_cntS; break;
        case 'G': ++s_cntG; break;
        case 'H': ++s_cntH; break;
        case 'F': ++s_cntF; break;
        case 'C': ++s_cntC; break;
        default: break;
        }
    }
}

/* 初始分工：浆果3 建造1 采木3 采石1（按距各资源点远近认领） */
static void assignInitialJobs(const tagInfo& inf)
{
    /* 建造工：任选一个（之后固定就是他） */
    int needB = 3, needW = 3, needS = 1, needC = 1;
    for (size_t i = 0; i < inf.farmers.size(); ++i) {
        const tagFarmer& f = inf.farmers[i];
        if (f.FarmerSort != FARMERTYPE_FARMER) continue;
        if (jobOf(f.SN)) continue;
        if (needC > 0) { s_job[f.SN] = 'C'; s_builderSN = f.SN; --needC; continue; }
        /* 采石工：离石头最近的人优先认领（简单起见按遍历顺序） */
        if (needS > 0) {
            bool hasStone = false;
            for (size_t j = 0; j < inf.resources.size(); ++j)
                if (inf.resources[j].Type == RESOURCE_STONE &&
                    inf.resources[j].Cnt > 0) { hasStone = true; break; }
            if (hasStone) { s_job[f.SN] = 'S'; --needS; continue; }
        }
        if (needW > 0) { s_job[f.SN] = 'W'; --needW; continue; }
        if (needB > 0) { s_job[f.SN] = 'B'; --needB; continue; }
    }
}

/* 场上是否还有存活的瞪羚（Cnt>0 的 RESOURCE_GAZELLE） */
static bool allGazelleDead(const tagInfo& inf)
{
    for (size_t i = 0; i < inf.resources.size(); ++i) {
        const tagResource& r = inf.resources[i];
        if (r.Type == RESOURCE_GAZELLE && r.Cnt > 0) return false;
    }
    return true;
}

/* 新村民按序列分配岗位；
 * 序列：2浆果 -> 6猎瞪羚 -> 3伐木 -> 之后按需分配（正常不会走到，只有补员才可能） */
static void assignSeqJobs(const tagInfo& inf)
{
    for (size_t i = 0; i < inf.farmers.size(); ++i) {
        const tagFarmer& f = inf.farmers[i];
        if (f.FarmerSort != FARMERTYPE_FARMER) continue;
        if (jobOf(f.SN)) continue;          // 已有岗位
        ++s_seqIdx;
        char j;
        if (s_seqIdx <= SEQ_BERRY_NUM)            j = 'B';   // 前2个采浆果
        else if (s_seqIdx <= SEQ_BERRY_NUM + SEQ_HUNT_NUM)
                                                  j = 'H';   // 接着6个猎瞪羚
        else if (s_seqIdx <= SEQ_BERRY_NUM + SEQ_HUNT_NUM + SEQ_WOOD_NUM)
                                                  j = 'W';   // 再3个伐木
        else {
            /* 序列用完后按需分配：农田不足->田，瞪羚还在->猎，否则伐木 */
            if (s_cntF < FARM_WORKER_NUM)          j = 'F';
            else if (!allGazelleDead(inf))         j = 'H';
            else                                   j = 'W';
        }
        s_job[f.SN] = j;
        s_jobOrder[f.SN] = s_seqIdx;
    }
}

/* 清理死亡村民的岗位记录；死亡补员时把序列号回退，保持岗位人数 */
static void cleanJobs(const tagInfo& inf)
{
    set<int> alive;
    for (size_t i = 0; i < inf.farmers.size(); ++i)
        alive.insert(inf.farmers[i].SN);
    vector<int> dead;
    for (map<int,char>::iterator it = s_job.begin(); it != s_job.end(); ++it)
        if (!alive.count(it->first)) dead.push_back(it->first);
    for (size_t k = 0; k < dead.size(); ++k) {
        int sn = dead[k];
        char j = s_job[sn];
        s_job.erase(sn);
        s_jobOrder.erase(sn);
        s_huntTarget.erase(sn);
        s_woodTree.erase(sn);
        s_farmerCmdFrame.erase(sn);
        s_farmerCmdId.erase(sn);
        s_farmerCmdTarget.erase(sn);
        s_farmerCmdKind.erase(sn);
        s_farmerStuck.erase(sn);
        /* 死亡补员：序列号回退1，让下一个新村民顶替同岗位 */
        if (s_seqIdx > 0) --s_seqIdx;
        (void)j;
    }
    if (s_builderSN >= 0 && !alive.count(s_builderSN)) {
        /* 建造工死了：优先从农田工/伐木工里挑最近的强制转岗接班 */
        const tagFarmer* best = NULL;
        double bd = 1e18;
        double tcx = blockCenter(s_tcDR), tcy = blockCenter(s_tcUR);
        for (size_t i = 0; i < inf.farmers.size(); ++i) {
            const tagFarmer& f = inf.farmers[i];
            if (f.FarmerSort != FARMERTYPE_FARMER) continue;
            char j = jobOf(f.SN);
            /* 只从采集岗里挑（不抢祭司）；农田工固定不动，不作为接班候选 */
            if (j != 'W' && j != 'B' && j != 'G' && j != 'H' && j != 'S')
                continue;
            double d = dist2(f.DR, f.UR, tcx, tcy);
            if (d < bd) { bd = d; best = &f; }
        }
        if (best) {
            s_job[best->SN] = 'C';
            s_builderSN = best->SN;
        } else {
            s_builderSN = -1;
        }
    }

    /* 清理树木归属：村民已死/已不伐木/树已采光的记录全部释放，
     * 让别的伐木工能认领，避免"树被占着却没人砍" */
    vector<int> dropTree;
    for (map<int,int>::iterator it = s_woodTree.begin();
         it != s_woodTree.end(); ++it) {
        int sn = it->first;
        if (!alive.count(sn) || jobOf(sn) != 'W') {
            dropTree.push_back(sn);
            continue;
        }
        bool ok = false;
        for (size_t i = 0; i < inf.resources.size(); ++i) {
            const tagResource& r = inf.resources[i];
            if (r.SN == it->second && r.Type == RESOURCE_TREE && r.Cnt > 0) {
                ok = true;
                break;
            }
        }
        if (!ok) dropTree.push_back(sn);
    }
    for (size_t i = 0; i < dropTree.size(); ++i)
        s_woodTree.erase(dropTree[i]);
}

/*----------------------------------------------------------------------------
 * 资源目标选择（按岗位）
 *--------------------------------------------------------------------------*/

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
    case RESOURCE_TREE:     return 1;   /* v6.3：一树一人，避免多个伐木工挤同一棵树 */
    case RESOURCE_BUSH:     return 3;
    case RESOURCE_STONE:    return 3;
    case RESOURCE_GOLD:     return 3;   /* v6.0：6人同采一处金矿，容量放宽到3 */
    case RESOURCE_GAZELLE:  return 2;
    case RESOURCE_ELEPHANT: return 3;
    default:                return 3;
    }
}

/* 就近选资源点 + 负载均衡：
 * 打分 = 距离² + 已有人数 * 拥挤惩罚（≈2格距离），
 * 让村民自动分散到人数少的资源点，缓解多人挤一个点造成的堵路/打转 */
static int nearestResOfType(const tagInfo& inf, double dr, double ur,
                            int type, int selfSN, int cap)
{
    int sn = -1;
    double best = 1e18;
    double crowdPenalty = (2.0 * s_bls) * (2.0 * s_bls);
    for (size_t i = 0; i < inf.resources.size(); ++i) {
        const tagResource& r = inf.resources[i];
        if ((int)r.Type != type || r.Cnt <= 0) continue;
        if (targetBad(inf, r.SN)) continue;
        int w = workersOnTarget(inf, r.SN, selfSN);
        if (w >= cap) continue;
        double score = dist2(dr, ur, r.DR, r.UR) + w * crowdPenalty;
        if (score < best) { best = score; sn = r.SN; }
    }
    return sn;
}

/* 伐木点（v6.3 一树一人）：
 *   1) 先沿用自己长期负责的那棵树（死了/被拉黑才换）
 *   2) 否则在"初始仓库 8 格内 + 没被别人认领"的树里挑最近的
 *   3) 还不够就跑去远处没人认领的树（宁可跑远，也不和别人挤一棵） */
static int nearestWoodForJob(const tagInfo& inf, double dr, double ur, int selfSN)
{
    /* 1) 自己的那棵树还在，且没被拉黑 -> 继续用它 */
    map<int,int>::iterator own = s_woodTree.find(selfSN);
    if (own != s_woodTree.end()) {
        int tsn = own->second;
        if (!targetBad(inf, tsn)) {
            for (size_t i = 0; i < inf.resources.size(); ++i) {
                const tagResource& r = inf.resources[i];
                if (r.SN != tsn) continue;
                if (r.Type == RESOURCE_TREE && r.Cnt > 0) return tsn;
                break;
            }
        }
        s_woodTree.erase(own);
    }

    /* 2) 收集已被其他伐木工认领的树 */
    set<int> claimed;
    for (map<int,int>::iterator t = s_woodTree.begin();
         t != s_woodTree.end(); ++t)
        if (t->first != selfSN) claimed.insert(t->second);

    int sn = -1;
    double best = 1e18;
    double crowdPenalty = (2.0 * s_bls) * (2.0 * s_bls);
    double lim = 8.0 * s_bls;

    /* 3a) 初始仓库 8 格内、无人认领的树 */
    if (s_stockDR >= 0) {
        double sx = blockCenter(s_stockDR), sy = blockCenter(s_stockUR);
        for (size_t i = 0; i < inf.resources.size(); ++i) {
            const tagResource& r = inf.resources[i];
            if ((int)r.Type != RESOURCE_TREE || r.Cnt <= 0) continue;
            if (targetBad(inf, r.SN)) continue;
            if (claimed.count(r.SN)) continue;
            if (dist2(r.DR, r.UR, sx, sy) > lim * lim) continue;  // 仓库8格内
            int w = workersOnTarget(inf, r.SN, selfSN);
            if (w >= resCap(RESOURCE_TREE)) continue;
            double score = dist2(dr, ur, r.DR, r.UR) + w * crowdPenalty;
            if (score < best) { best = score; sn = r.SN; }
        }
    }
    /* 3b) 仓库附近没空树了：去远处找无人认领的树 */
    if (sn < 0) {
        for (size_t i = 0; i < inf.resources.size(); ++i) {
            const tagResource& r = inf.resources[i];
            if ((int)r.Type != RESOURCE_TREE || r.Cnt <= 0) continue;
            if (targetBad(inf, r.SN)) continue;
            if (claimed.count(r.SN)) continue;
            int w = workersOnTarget(inf, r.SN, selfSN);
            if (w >= resCap(RESOURCE_TREE)) continue;
            double score = dist2(dr, ur, r.DR, r.UR) + w * crowdPenalty;
            if (score < best) { best = score; sn = r.SN; }
        }
    }
    if (sn >= 0) s_woodTree[selfSN] = sn;   // 认领这棵树
    return sn;
}

/* 农田目标：一块田恰好1人（多了不增产），0人的田优先补 */
static int nearestFarmForJob(const tagInfo& inf, double dr, double ur, int selfSN)
{
    int sn = -1;
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

/* 猎人目标：先打光整组瞪羚再采肉。
 * 给每个猎人锁定一只不同的活瞪羚去攻击（1对1），
 * 全组死光（都变成可采尸体）后再统一采肉。 */
static int pickHuntTarget(const tagInfo& inf, int selfSN)
{
    /* 先按 SN 找到自己（注意：selfSN 是唯一标识，不能直接当数组下标用！） */
    double selfDR = 0, selfUR = 0;
    bool foundSelf = false;
    for (size_t i = 0; i < inf.farmers.size(); ++i) {
        if (inf.farmers[i].SN == selfSN) {
            selfDR = inf.farmers[i].DR;
            selfUR = inf.farmers[i].UR;
            foundSelf = true;
            break;
        }
    }
    if (!foundSelf) return -1;

    /* 已锁定且目标还在 -> 继续打它 */
    map<int,int>::iterator it = s_huntTarget.find(selfSN);
    if (it != s_huntTarget.end()) {
        for (size_t i = 0; i < inf.resources.size(); ++i) {
            const tagResource& r = inf.resources[i];
            if (r.SN == it->second && r.Type == RESOURCE_GAZELLE && r.Cnt > 0)
                return it->second;
        }
        s_huntTarget.erase(it);
    }
    /* 优先找一只没被其他猎人锁定的活瞪羚（1对1，不抢别人的） */
    int sn = -1;
    double bd = 1e18;
    set<int> taken;
    for (map<int,int>::iterator t = s_huntTarget.begin();
         t != s_huntTarget.end(); ++t)
        taken.insert(t->second);
    for (size_t i = 0; i < inf.resources.size(); ++i) {
        const tagResource& r = inf.resources[i];
        if (r.Type != RESOURCE_GAZELLE || r.Cnt <= 0) continue;
        if (taken.count(r.SN)) continue;
        if (targetBad(inf, r.SN)) continue;
        double d = dist2(selfDR, selfUR, r.DR, r.UR);
        if (d < bd) { bd = d; sn = r.SN; }
    }
    /* 活瞪羚数量少于猎人数时：所有瞪羚都被锁了，
     * 就退而求其次去打最近的那只（多人围殴同一只），
     * 避免有人没目标而被挤去采金/伐木 */
    if (sn < 0) {
        for (size_t i = 0; i < inf.resources.size(); ++i) {
            const tagResource& r = inf.resources[i];
            if (r.Type != RESOURCE_GAZELLE || r.Cnt <= 0) continue;
            if (targetBad(inf, r.SN)) continue;
            double d = dist2(selfDR, selfUR, r.DR, r.UR);
            if (d < bd) { bd = d; sn = r.SN; }
        }
    }
    if (sn >= 0) s_huntTarget[selfSN] = sn;
    return sn;
}

/* 瞪羚是否全部死光（只剩可采尸体）——用"是否还有瞪羚在跑"近似：
 * 活瞪羚会移动；这里简化为：场上瞪羚数>0 且猎人还没打够轮次就继续打。
 * 实际实现：猎人指令用 HumanAction(瞪羚SN)，内核对动物是"猎杀+采集"一体，
 * 打死自动转采集。为执行"先全打死再采"，猎人锁定目标后反复下令攻击即可。 */

/* 主金矿 = 离市政中心最近的那处金矿（采金岗、金矿仓库、抽调伐木工都以它为准） */
static const tagResource* mainGold(const tagInfo& inf)
{
    const tagResource* best = NULL;
    double bd = 1e18;
    double tcx = blockCenter(s_tcDR), tcy = blockCenter(s_tcUR);
    for (size_t i = 0; i < inf.resources.size(); ++i) {
        const tagResource& r = inf.resources[i];
        if (r.Type != RESOURCE_GOLD || r.Cnt <= 0) continue;
        double d = dist2(tcx, tcy, r.DR, r.UR);
        if (d < bd) { bd = d; best = &r; }
    }
    return best;
}

/*----------------------------------------------------------------------------
 * 3. 村民管理（v6.0 岗位驱动）
 *    逃跑 > 上交 > 按岗位干活 > 兜底开视野
 *--------------------------------------------------------------------------*/
void UsrAI::manageFarmers(const tagInfo& inf)
{
    /* v6.5：本版本村民不再躲避敌军（已删除撤退逻辑） */

    /* 升铜器后：从伐木工里抽调离主金矿最近的 3 人转去采金，
     * 补齐到 GOLD_WORKER_TARGET（猎人转的 3 人 + 抽调的 3 人 = 6） */
    if (isBronze(inf) && s_goldFound && s_cntG < GOLD_WORKER_TARGET) {
        const tagResource* gold = mainGold(inf);
        if (gold) {
            const tagFarmer* best = NULL;
            double bd = 1e18;
            for (size_t i = 0; i < inf.farmers.size(); ++i) {
                const tagFarmer& f = inf.farmers[i];
                if (f.FarmerSort != FARMERTYPE_FARMER) continue;
                if (jobOf(f.SN) != 'W') continue;       // 只从伐木工里抽
                if (f.SN == s_builderSN && !s_builderRetired) continue;
                double d = dist2(f.DR, f.UR, gold->DR, gold->UR);
                if (d < bd) { bd = d; best = &f; }
            }
            if (best) s_job[best->SN] = 'G';   // 每帧抽 1 个，几帧内补齐 3 个
        }
    }

    /* 本帧实时采金人数（s_cntG 只在帧首统计，同帧多人转岗会算不准） */
    int goldAssigned = s_cntG;

    for (size_t i = 0; i < inf.farmers.size(); ++i) {
        const tagFarmer& f = inf.farmers[i];
        if (f.FarmerSort != FARMERTYPE_FARMER) continue;

        /* 核对上一条指令结果 */
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

        /* 建造工由 manageBuild 指挥，这里跳过 */
        if (f.SN == s_builderSN && !s_builderRetired) continue;
        if (s_pend.id >= 0 && s_pend.builderSN == f.SN) continue;
        if (f.NowState != HUMAN_STATE_IDLE) continue;

        /* 指令冷却 */
        int lastFrame = -999;
        { map<int,int>::iterator it = s_farmerCmdFrame.find(f.SN);
          if (it != s_farmerCmdFrame.end()) lastFrame = it->second; }
        if (inf.GameFrame - lastFrame < 12) continue;

        int lastKind = 0, lastTarget = -1;
        { map<int,char>::iterator it = s_farmerCmdKind.find(f.SN);
          if (it != s_farmerCmdKind.end()) lastKind = it->second; }
        { map<int,int>::iterator it = s_farmerCmdTarget.find(f.SN);
          if (it != s_farmerCmdTarget.end()) lastTarget = it->second; }

        /* 快速回空闲 = 目标有问题 */
        bool quickReturn = (inf.GameFrame - lastFrame < 300);
        if (quickReturn) {
            if (lastKind == 'G' || lastKind == 'M') s_farmerStuck[f.SN] += 1;
        } else {
            s_farmerStuck[f.SN] = 0;
        }

        /* 卡住3次：把上次的目标临时拉黑（换一个资源点），并小幅挪动脱离碰撞，
         * 避免对同一个点反复下令 -> 路径反复重置 -> 原地打转 */
        int stuck = 0;
        { map<int,int>::iterator it = s_farmerStuck.find(f.SN);
          if (it != s_farmerStuck.end()) stuck = it->second; }
        if (stuck >= 3) {
            if (lastTarget > 0)
                s_targetBadUntil[lastTarget] = inf.GameFrame + 900;
            double ang = ((f.SN * 37 + inf.GameFrame * 11) % 360) * 3.14159265 / 180.0;
            double tx = f.DR + cos(ang) * 2.0 * s_bls;
            double ty = f.UR + sin(ang) * 2.0 * s_bls;
            clampDetail(tx, ty);
            HumanMove(f.SN, tx, ty);
            noteFarmerCmd(f.SN, -1, -1, 'M', inf.GameFrame);
            s_farmerStuck[f.SN] = 0;
            continue;
        }

        /* 2) 手持资源 -> 上交
         * 浆果/肉(STOCKFOOD)交仓库；农田食物(GRANARYFOOD)交谷仓；
         * 木石金交仓库；找不到就交市镇中心 */
        if (f.Resource > 0) {
            int wantType = BUILDING_STOCK;
            if (f.ResourceSort == HUMAN_GRANARYFOOD) wantType = BUILDING_GRANARY;
            const tagBuilding* depot = nearestBuilding(inf, wantType, f.DR, f.UR, true);
            if (!depot || targetBad(inf, depot->SN))
                depot = nearestBuilding(inf, BUILDING_CENTER, f.DR, f.UR, true);
            if (depot) {
                int id = HumanAction(f.SN, depot->SN);
                noteFarmerCmd(f.SN, id, depot->SN, 'D', inf.GameFrame);
            }
            continue;
        }

        /* 3) 按岗位派活 */
        char job = jobOf(f.SN);
        int sn = -1;
        int exclude = (quickReturn && lastKind == 'G') ? lastTarget : -1;
        if (exclude > 0) s_targetBadUntil[exclude] = inf.GameFrame + 300;

        if (job == 'B') {
            /* 浆果岗：浆果采光 -> 转去伐木（木头够后由伐木工再去建农田） */
            sn = nearestResOfType(inf, f.DR, f.UR, RESOURCE_BUSH, f.SN,
                                  resCap(RESOURCE_BUSH));
            if (sn < 0) {
                s_job[f.SN] = 'W';
                job = 'W';
                sn = nearestWoodForJob(inf, f.DR, f.UR, f.SN);
            }
        }
        if (job == 'H') {
            /* 猎瞪羚岗：锁定一只瞪羚反复攻击（打死自动采肉）；
             * 若活瞪羚少于猎人数，pickHuntTarget 会让多人围殴同一只 */
            sn = pickHuntTarget(inf, f.SN);
            if (sn < 0) {
                if (!s_gazelleFound && inf.GameFrame < GAZELLE_GIVEUP_FRAME) {
                    /* v6.6：瞪羚还没探明 -> 保持 'H' 岗位，绝不转岗！
                     * 此时会落到下面的兜底逻辑（去探索边界开视野），
                     * 6 个猎人自动帮忙开图找瞪羚；一旦探到就立刻猎杀 */
                } else {
                    /* 瞪羚已探明且肉都采完（或超时放弃）：3金3木转岗 */
                    if (goldAssigned < HUNT_TO_GOLD) {
                        s_job[f.SN] = 'G';
                        ++goldAssigned;
                    } else {
                        s_job[f.SN] = 'W';
                    }
                    job = jobOf(f.SN);
                }
            }
        }
        if (job == 'W') {
            sn = nearestWoodForJob(inf, f.DR, f.UR, f.SN);
        } else if (job == 'S') {
            sn = nearestResOfType(inf, f.DR, f.UR, RESOURCE_STONE, f.SN,
                                  resCap(RESOURCE_STONE));
            /* 石头采够了（库存>=阈值）就转伐木 */
            if (inf.Stone >= STONE_ENOUGH) { s_job[f.SN] = 'W'; job = 'W';
                sn = nearestWoodForJob(inf, f.DR, f.UR, f.SN); }
        } else if (job == 'G') {
            /* 采金岗：就近选金矿 + 负载均衡，
             * 避免多个采金工全挤在同一处金矿互相堵路 */
            sn = nearestResOfType(inf, f.DR, f.UR, RESOURCE_GOLD, f.SN,
                                  resCap(RESOURCE_GOLD));
            if (sn < 0) {
                /* 所有金矿都满员：允许超员，退回最近的金矿继续采 */
                sn = nearestResOfType(inf, f.DR, f.UR, RESOURCE_GOLD, f.SN, 99);
            }
        } else if (job == 'F') {
            sn = nearestFarmForJob(inf, f.DR, f.UR, f.SN);
        } else if (job == 'B') {
            sn = nearestResOfType(inf, f.DR, f.UR, RESOURCE_BUSH, f.SN,
                                  resCap(RESOURCE_BUSH));
        }

        if (sn >= 0) {
            int id = HumanAction(f.SN, sn);
            noteFarmerCmd(f.SN, id, sn, 'G', inf.GameFrame);
            continue;
        }

        /* 4) 岗位目标暂时不存在（如农田还没建好）：
         *    农田工 -> 去农田锚点附近等；其他 -> 探索边界开视野 */
        if (job == 'F') {
            /* 田还没建：在市政中心附近待命，别乱跑 */
            const tagBuilding* tc = nearestBuilding(inf, BUILDING_CENTER,
                                                    f.DR, f.UR, true);
            if (tc && inf.GameFrame - lastFrame >= 120) {
                HumanMove(f.SN, blockCenter(tc->BlockDR),
                          blockCenter(tc->BlockUR));
                noteFarmerCmd(f.SN, -1, -1, 'M', inf.GameFrame);
            }
            continue;
        }
        int fdr = -1, fur = -1;
        double minD = 2.0 * s_bls;
        {   /* 简化版找边界：直接用 frontier 列表 */
            double bd = 1e18;
            for (size_t k = 0; k < s_frontier.size(); ++k) {
                int kx = s_frontier[k].first, ky = s_frontier[k].second;
                double tx = blockCenter(kx), ty = blockCenter(ky);
                double d = dist2(f.DR, f.UR, tx, ty);
                if (d < minD * minD) continue;
                if (d < bd) { bd = d; fdr = kx; fur = ky; }
            }
        }
        if (fdr >= 0) {
            HumanMove(f.SN, blockCenter(fdr), blockCenter(fur));
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
 * 1. 建造流水线（全程只有1个专职建造工 s_builderSN）
 *    固定顺序（v6.5）：
 *      2房 -> 市场 -> 箭塔 -> 2房 -> 兵营 -> 靶场 -> 2房 -> 马厩 -> 学院
 *      -> 之后"按需建房"（人口余量 <=4 才补房，这些房是给造兵留人口的）
 *    木材优先级（马厩之后）：金矿旁仓库 > 农田
 *    另有两类建造不占流水线，由就近空闲村民顺路完成：
 *      瞪羚群旁仓库x1、金矿旁仓库x1(v6.3延后)、农田10块
 *      (农田采光后由失去农田的农田工自己重建，见 0.5 段)
 *--------------------------------------------------------------------------*/

/* 定点仓库在途（独立槽位，避免阻塞流水线） */
static PendBuild s_pendStock;

/* 农田在途 */
static int s_farmPendId = -1;
static int s_farmPendFrame = -9999;
static int s_farmPendSN = -1;
static int s_farmPendDR = -1, s_farmPendUR = -1;
static bool s_farmPendInPlace = false;         // 本单是否为"原地重建"

/* 农田落点记录（v6.6：采光被回收后原地重建用） */
static vector<pair<int,int> > s_farmSpots;     // 已建农田的落点
static set<int> s_farmSpotBad;                 // 原地重建失败过的落点

void UsrAI::manageBuild(const tagInfo& inf)
{
    if (s_tcDR < 0) return;

    /* 0) 流水线在途指令的结果核查 */
    if (s_pend.id >= 0) {
        map<int,int>::const_iterator it = inf.ins_ret.find(s_pend.id);
        bool hasRet = (it != inf.ins_ret.end());
        bool timeout = (inf.GameFrame - s_pend.frame > 900);
        if (hasRet || timeout) {
            int w = bsize(s_pend.type < 0 ? BUILDING_HOME : s_pend.type);
            if (hasRet && it->second == ACTION_SUCCESS) {
                /* 成功：建筑实体出现后自然占用该位置 */
            } else if (hasRet) {
                /* 未解锁说明位置没问题（只是前置没到），不拉黑坐标 */
                if (it->second != ACTION_INVALID_HUMANBUILD_LOCK) {
                    for (int i = 0; i < w; ++i)
                        for (int j = 0; j < w; ++j)
                            s_badSpot.insert(bkey(s_pend.dr + i, s_pend.ur + j));
                }
                s_buildTypeCdUntil[s_pend.type] = inf.GameFrame + 300;
            } else {
                /* 超时多为建造者被打断，先临时跳过这个点 */
                s_spotSkipUntil[bkey(s_pend.dr, s_pend.ur)] = inf.GameFrame + 1200;
            }
            s_pend.id = -1;
            s_pend.type = -1;
            s_pend.builderSN = -1;
        }
    }

    /* 0.2) 定点仓库在途结果核查 */
    if (s_pendStock.id >= 0) {
        map<int,int>::const_iterator it = inf.ins_ret.find(s_pendStock.id);
        bool hasRet = (it != inf.ins_ret.end());
        if (hasRet || inf.GameFrame - s_pendStock.frame > 900) {
            if (hasRet && it->second != ACTION_SUCCESS &&
                it->second != ACTION_INVALID_HUMANBUILD_LOCK) {
                int w = bsize(s_pendStock.type);
                for (int i = 0; i < w; ++i)
                    for (int j = 0; j < w; ++j)
                        s_badSpot.insert(bkey(s_pendStock.dr + i, s_pendStock.ur + j));
            }
            s_pendStock.id = -1;
            s_pendStock.type = -1;
            s_pendStock.builderSN = -1;
        }
    }

    /* 0.4) 农田在途结果核查 */
    if (s_farmPendId >= 0) {
        map<int,int>::const_iterator it = inf.ins_ret.find(s_farmPendId);
        if (it != inf.ins_ret.end() ||
            inf.GameFrame - s_farmPendFrame > 900) {
            if (it != inf.ins_ret.end()) {
                if (it->second == ACTION_SUCCESS) {
                    /* 建田成功：该村民转为农田工，固定耕种这块田；
                     * 同时记下落点（供采光回收后原地重建） */
                    if (s_farmPendSN >= 0) s_job[s_farmPendSN] = 'F';
                    if (s_farmPendDR >= 0) {
                        bool has = false;
                        for (size_t k = 0; k < s_farmSpots.size(); ++k)
                            if (s_farmSpots[k].first == s_farmPendDR &&
                                s_farmSpots[k].second == s_farmPendUR) { has = true; break; }
                        if (!has)
                            s_farmSpots.push_back(make_pair(s_farmPendDR, s_farmPendUR));
                    }
                } else if (it->second != ACTION_INVALID_HUMANBUILD_LOCK) {
                    s_buildTypeCdUntil[BUILDING_FARM] = inf.GameFrame + 300;
                    /* 原地重建失败：把这个落点拉黑，下次改用正常选址 */
                    if (s_farmPendInPlace && s_farmPendDR >= 0)
                        s_farmSpotBad.insert(bkey(s_farmPendDR, s_farmPendUR));
                }
            }
            s_farmPendId = -1;
            s_farmPendSN = -1;
            s_farmPendDR = -1;
            s_farmPendUR = -1;
            s_farmPendInPlace = false;
        }
    }

    /* 0.5) 农田建造：浆果采光 + 木材够用后，从伐木工中抽调村民修建；
     *      建完该村民转为农田工固定耕种。共 10 块 = 5 块围谷仓 + 5 块围市政中心 */
    bool berryGone = true;
    for (size_t i = 0; i < inf.resources.size(); ++i)
        if (inf.resources[i].Type == RESOURCE_BUSH &&
            inf.resources[i].Cnt > 0) { berryGone = false; break; }

    /* v6.5 木材优先级（马厩之后）：先补"金矿旁仓库"，其次才是农田。
     * 只要金矿旁仓库还没建好、且木材够建仓，就先把木材让给它 */
    bool goldStockPending = false;
    if (!s_stockGoldDone && s_goldFound && inf.Wood >= 120 &&
        (isBronze(inf) || s_cntG > 0)) {
        const tagResource* g = mainGold(inf);
        if (g && !hasStoreNearby(inf, BUILDING_STOCK, g->DR, g->UR, 7.0 * s_bls))
            goldStockPending = true;
    }

    int farmExisting = countLiveFarms(inf);
    if (berryGone && s_farmPendId < 0 &&
        !goldStockPending &&
        inf.Wood >= FARM_WOOD_MIN &&
        countAnyBuilding(inf, BUILDING_MARKET) > 0 &&
        farmExisting < FARM_TOTAL) {
        /* v6.6：先看有没有"已消失农田的原落点"——有就原地重建，不重新选址 */
        int dr = -1, ur = -1;
        bool inPlace = false;
        for (size_t k = 0; k < s_farmSpots.size() && dr < 0; ++k) {
            int sdr = s_farmSpots[k].first, sur = s_farmSpots[k].second;
            if (s_farmSpotBad.count(bkey(sdr, sur))) continue;   // 原地失败过的点不再试
            bool exists = false;
            for (size_t j = 0; j < inf.buildings.size(); ++j) {
                const tagBuilding& b = inf.buildings[j];
                if (b.Type == BUILDING_FARM && b.BlockDR == sdr &&
                    b.BlockUR == sur) { exists = true; break; }
            }
            if (!exists) { dr = sdr; ur = sur; inPlace = true; }
        }
        /* 没有可原地重建的点 -> 走正常螺旋选址 */
        if (dr < 0) {
            int anchorDR, anchorUR;
            /* 前5块锚定谷仓，后5块锚定市政中心 */
            if (farmExisting < FARM_PER_ANCHOR && s_granaryDR >= 0) {
                anchorDR = s_granaryDR; anchorUR = s_granaryUR;
            } else {
                anchorDR = s_tcDR;      anchorUR = s_tcUR;
            }
            if (!findBuildSpotFarm(inf, anchorDR, anchorUR, dr, ur)) dr = -1;
        }
        if (dr >= 0) {
            /* 优先让"失去农田的空闲农田工"自己重建这块田（建好后继续耕种，
             * 也不占用伐木工）；没有空闲农田工再退回去找伐木工 */
            const tagFarmer* fbF = NULL;   // 空闲农田工
            const tagFarmer* fbW = NULL;   // 空闲伐木工
            double bdF = 1e18, bdW = 1e18;
            double cx = blockCenter(dr), cy = blockCenter(ur);
            for (size_t i = 0; i < inf.farmers.size(); ++i) {
                const tagFarmer& f = inf.farmers[i];
                if (f.FarmerSort != FARMERTYPE_FARMER) continue;
                if (f.NowState != HUMAN_STATE_IDLE) continue;
                if (f.SN == s_builderSN && !s_builderRetired) continue;
                if (s_pend.id >= 0 && s_pend.builderSN == f.SN) continue;
                if (s_pendStock.id >= 0 && s_pendStock.builderSN == f.SN) continue;
                char j = jobOf(f.SN);
                double d = dist2(f.DR, f.UR, cx, cy);
                if (j == 'F')      { if (d < bdF) { bdF = d; fbF = &f; } }
                else if (j == 'W') { if (d < bdW) { bdW = d; fbW = &f; } }
            }
            const tagFarmer* fb = fbF ? fbF : fbW;
            if (fb) {
                int id = HumanBuild(fb->SN, BUILDING_FARM, dr, ur);
                s_farmPendId = id;
                s_farmPendFrame = inf.GameFrame;
                s_farmPendSN = fb->SN;
                s_farmPendDR = dr;
                s_farmPendUR = ur;
                s_farmPendInPlace = inPlace;
                noteFarmerCmd(fb->SN, id, -1, 'M', inf.GameFrame);
            }
        }
    }

    /* 0.6) 两处定点仓库（各只建一次）：瞪羚群旁、金矿旁
     * 仓库收肉(STOCKFOOD)和金，符合引擎设定（Building.cpp:563） */
    if (s_pendStock.id < 0 && inf.Wood >= 120) {
        int wantStock = -1;
        double ax = 0, ay = 0;
        bool isGazelle = false;

        if (!s_stockGazelleDone) {
            /* 瞪羚群中心（含尸体，位置不变）——只要有瞪羚就建仓 */
            double sx = 0, sy = 0; int n = 0;
            for (size_t i = 0; i < inf.resources.size(); ++i) {
                const tagResource& r = inf.resources[i];
                if (r.Type != RESOURCE_GAZELLE) continue;
                sx += r.DR; sy += r.UR; ++n;
            }
            if (n >= 1) {
                wantStock = BUILDING_STOCK;
                ax = sx / n; ay = sy / n;
                isGazelle = true;
            }
        }
        /* 金矿仓库（v6.3 延后）：等"已经开始采金"或"已升铜器"之后才建，
         * 避免前期把木材浪费在一个暂时用不上的仓库上 */
        bool goldPhase = isBronze(inf) || s_cntG > 0;
        if (wantStock < 0 && !s_stockGoldDone && s_goldFound && goldPhase) {
            const tagResource* bestG = mainGold(inf);
            if (bestG) {
                wantStock = BUILDING_STOCK;
                ax = bestG->DR; ay = bestG->UR;
                isGazelle = false;
            }
        }

        if (wantStock >= 0 &&
            !hasStoreNearby(inf, BUILDING_STOCK, ax, ay, 7.0 * s_bls)) {
            /* 金矿仓库：锚点偏移2格，确保与金矿间隔≥1单位便于通行 */
            int adr = (int)(ax / s_bls);
            int aur = (int)(ay / s_bls);
            if (!isGazelle) { adr += 2; aur += 2; }
            int dr = -1, ur = -1;
            if (findBuildSpot(inf, wantStock, adr, aur, dr, ur)) {
                const tagFarmer* fb = NULL;
                double bd = 1e18;
                double cx = blockCenter(dr), cy = blockCenter(ur);
                for (size_t i = 0; i < inf.farmers.size(); ++i) {
                    const tagFarmer& f = inf.farmers[i];
                    if (f.FarmerSort != FARMERTYPE_FARMER) continue;
                    if (f.NowState != HUMAN_STATE_IDLE) continue;
                    if (f.SN == s_builderSN && !s_builderRetired) continue;
                    if (s_pend.id >= 0 && s_pend.builderSN == f.SN) continue;
                    if (s_farmPendSN >= 0 && s_farmPendSN == f.SN) continue;
                    double d = dist2(f.DR, f.UR, cx, cy);
                    if (d < bd) { bd = d; fb = &f; }
                }
                if (fb) {
                    int id = HumanBuild(fb->SN, wantStock, dr, ur);
                    s_pendStock.id = id;
                    s_pendStock.type = wantStock;
                    s_pendStock.dr = dr; s_pendStock.ur = ur;
                    s_pendStock.frame = inf.GameFrame;
                    s_pendStock.builderSN = fb->SN;
                    noteFarmerCmd(fb->SN, id, -1, 'M', inf.GameFrame);
                    /* 下单成功才置标志，避免选址失败/无空闲村民导致永久漏建 */
                    if (isGazelle) s_stockGazelleDone = true;
                    else           s_stockGoldDone    = true;
                }
            }
        }
    }

    /* 1) 烂尾续建：在建建筑无人施工 -> 派最近空闲村民续建
     * （HumanAction 己方未完工建筑，内核走 FixBuilding 续建流程） */
    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        const tagBuilding& b = inf.buildings[i];
        if (b.Percent >= 100) continue;
        bool hasWorker = false;
        for (size_t j = 0; j < inf.farmers.size() && !hasWorker; ++j) {
            const tagFarmer& f = inf.farmers[j];
            if (f.FarmerSort != FARMERTYPE_FARMER) continue;
            if (f.WorkObjectSN == b.SN && f.NowState != HUMAN_STATE_IDLE)
                hasWorker = true;
        }
        if (hasWorker) continue;

        static map<int,int> fixCd;         // 续建节流
        int lastFix = -9999;
        map<int,int>::iterator fc = fixCd.find(b.SN);
        if (fc != fixCd.end()) lastFix = fc->second;
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
        fixCd[b.SN] = inf.GameFrame;
        noteFarmerCmd(fb->SN, id, b.SN, 'M', inf.GameFrame);
    }

    /* 2) 流水线主体（建造工执行） */
    if (s_builderRetired || s_builderSN < 0) return;
    if (s_pend.id >= 0) return;            // 上一单还没结果

    const tagFarmer* builder = NULL;
    for (size_t i = 0; i < inf.farmers.size(); ++i)
        if (inf.farmers[i].SN == s_builderSN) { builder = &inf.farmers[i]; break; }
    if (!builder) return;
    if (builder->NowState != HUMAN_STATE_IDLE) return;
    /* v6.5：不再因为"敌人贴近"就中断建造（村民统一不躲避敌军） */

    bool bronze = isBronze(inf);

    int want = -1;
    int ax = s_tcDR, ay = s_tcUR;
    bool useTowerSpot = false, useEdgeSpot = false;

    /* v6.2 固定建造顺序（不再按人口插队建房，避免连续建房拖延后续建筑）：
     * 2房 -> 市场 -> 箭塔 -> 2房 -> 兵营 -> 靶场 -> 2房 -> 马厩 -> 2房 -> 学院 -> 补足12房 */
    switch (s_buildStep) {
    case STEP_HOME2:
        if (s_homeBuiltByMe < 2 && inf.Wood >= 30) {
            want = BUILDING_HOME;
            useEdgeSpot = true;            // 开局2房建边缘
        } else {
            s_buildStep = STEP_MARKET;     // 2座已下单，立刻去建市场
        }
        break;
    case STEP_MARKET:
        if (countAnyBuilding(inf, BUILDING_MARKET) > 0) {
            s_buildStep = STEP_TOWER;      // 市场建好 -> 建箭塔
        } else if (inf.Wood >= 150) {
            want = BUILDING_MARKET;
            useEdgeSpot = true;
        }
        break;
    case STEP_TOWER:
        if (countAnyBuilding(inf, BUILDING_ARROWTOWER) >= TOWER_TARGET) {
            s_buildStep = STEP_HOME2B;
        } else if (s_res[R_TOWER_UNLOCK].done && inf.Stone >= TOWER_STONE_COST) {
            want = BUILDING_ARROWTOWER;
            if (s_twDR >= 0) { ax = s_twDR; ay = s_twUR; }   // 初始塔附近
            useTowerSpot = true;
        }
        break;
    case STEP_HOME2B:
        if (s_homeBuiltByMe < 4 && inf.Wood >= 30) {
            want = BUILDING_HOME;          // 市场+箭塔后的2房
            useEdgeSpot = true;
        } else {
            s_buildStep = STEP_ARMYCAMP;
        }
        break;
    case STEP_ARMYCAMP:
        if (countAnyBuilding(inf, BUILDING_ARMYCAMP) > 0) {
            s_buildStep = STEP_RANGE;
        } else if (inf.Wood >= 125) {
            want = BUILDING_ARMYCAMP;
            useEdgeSpot = true;
        }
        break;
    case STEP_RANGE:
        if (countAnyBuilding(inf, BUILDING_RANGE) > 0) {
            s_buildStep = STEP_STABLE;     // v6.6：靶场建好直接建马厩
        } else if (countAnyBuilding(inf, BUILDING_ARMYCAMP) > 0 &&
                   inf.Wood >= 150) {
            want = BUILDING_RANGE;
            useEdgeSpot = true;
        }
        break;
    case STEP_STABLE:
        if (countAnyBuilding(inf, BUILDING_STABLE) > 0) {
            s_buildStep = STEP_COLLAGE;
        } else if (countAnyBuilding(inf, BUILDING_RANGE) > 0 &&
                   inf.Wood >= 150) {
            want = BUILDING_STABLE;
            useEdgeSpot = true;
        }
        break;
    case STEP_COLLAGE:
        /* 学院需铜器 + 马厩 */
        if (countAnyBuilding(inf, BUILDING_COLLAGE) > 0) {
            s_buildStep = STEP_HOMEDEMAND;
        } else if (bronze && countAnyBuilding(inf, BUILDING_STABLE) > 0 &&
                   inf.Wood >= 180) {
            want = BUILDING_COLLAGE;
            useEdgeSpot = true;
        }
        break;
    case STEP_HOMEDEMAND:
        /* v6.5：马厩/学院之后不再固定建房，改为"按需"——
         * 人口余量 <=4 就补 1 座房屋（这些房屋是给造兵留人口的） */
        if (countAnyBuilding(inf, BUILDING_HOME) < HOME_TARGET &&
            inf.Human_MaxNum - inf.Human_Num <= 4 &&
            inf.Wood >= 30) {
            want = BUILDING_HOME;
            useEdgeSpot = true;
        }
        break;
    default:
        /* 流水线完工：建造工退休，转岗采金 */
        s_builderRetired = true;
        if (s_builderSN >= 0) s_job[s_builderSN] = 'G';
        return;
    }

    /* 2.5) 资源不足时让建造工去采集所需材料，避免发呆 */
    if (want >= 0) {
        bool needWood = false, needStone = false;
        if (want == BUILDING_HOME)            needWood = (inf.Wood < 30);
        else if (want == BUILDING_ARROWTOWER) needStone = (inf.Stone < TOWER_STONE_COST);
        else if (want == BUILDING_MARKET)     needWood = (inf.Wood < 150);
        else if (want == BUILDING_ARMYCAMP)   needWood = (inf.Wood < 125);
        else if (want == BUILDING_RANGE)      needWood = (inf.Wood < 150);
        else if (want == BUILDING_STABLE)     needWood = (inf.Wood < 150);
        else if (want == BUILDING_COLLAGE)    needWood = (inf.Wood < 180);

        if (needWood || needStone) {
            int needSN = -1;
            if (needWood) {
                needSN = nearestWoodForJob(inf, builder->DR, builder->UR, builder->SN);
            } else {
                needSN = nearestResOfType(inf, builder->DR, builder->UR,
                                          RESOURCE_STONE, builder->SN,
                                          resCap(RESOURCE_STONE));
            }
            if (needSN >= 0) {
                int id = HumanAction(builder->SN, needSN);
                noteFarmerCmd(builder->SN, id, needSN, 'G', inf.GameFrame);
            }
            return;
        }
    }

    if (want < 0) return;

    /* 3) 选址 */
    int dr = -1, ur = -1;
    if (useTowerSpot) {
        if (!findBuildSpotTower(inf, ax, ay, dr, ur)) return;
    } else if (useEdgeSpot) {
        /* 兵营/靶场：边缘 + 距谷仓≥20格，防堵路 */
        if (want == BUILDING_ARMYCAMP || want == BUILDING_RANGE) {
            if (!findBuildSpotEdgeFar(inf, want, 20.0 * s_bls, dr, ur)) {
                if (!findBuildSpotEdge(inf, want, dr, ur)) {
                    if (!findBuildSpot(inf, want, ax, ay, dr, ur)) return;
                }
            }
        } else {
            if (!findBuildSpotEdge(inf, want, dr, ur)) {
                if (!findBuildSpot(inf, want, ax, ay, dr, ur)) return;
            }
        }
    } else if (!findBuildSpot(inf, want, ax, ay, dr, ur)) {
        return;
    }

    /* 4) 下单 */
    int id = HumanBuild(builder->SN, want, dr, ur);
    s_pend.id = id;
    s_pend.type = want;
    s_pend.dr = dr;
    s_pend.ur = ur;
    s_pend.frame = inf.GameFrame;
    s_pend.builderSN = builder->SN;
    noteFarmerCmd(builder->SN, id, -1, 'M', inf.GameFrame);
    if (want == BUILDING_HOME)
        ++s_homeBuiltByMe;      // 流水线累计建房计数（v6.6 共4座，其余按需补到12）
}

/*----------------------------------------------------------------------------
 * 2. 建筑行动：科技 / 造村民 / 三种兵 / 升时代
 *
 * v6.0 只造三种兵（造到人口上限为止）：
 *   复合弓手（靶场）：铜器 + 复合弓科技，40食+20金
 *   骑兵（马厩）　　：铜器，70食+80金
 *   方阵兵（学院）　：铜器，60食+40金
 *   兵营不造任何兵（仅作为靶场/马厩的前置建筑存在）
 * 注意：铜器时代前这三种兵都造不出来（引擎前置，见 Development.cpp），
 *       所以前期防守只能靠 2 座箭塔 + 祭司转化 + 村民逃命。
 *--------------------------------------------------------------------------*/
void UsrAI::manageBuildingActions(const tagInfo& inf)
{
    /* 科技指令结果核查（ins_ret 窗口短，必须每帧最前） */
    for (int i = 0; i < R_NUM; ++i) {
        if (s_res[i].id < 0 || s_res[i].done) continue;
        map<int,int>::const_iterator it = inf.ins_ret.find(s_res[i].id);
        if (it != inf.ins_ret.end()) {
            if (it->second == ACTION_SUCCESS) s_res[i].done = true;
            else s_res[i].cdUntil = inf.GameFrame + 600;
            s_res[i].id = -1;
        } else if (inf.GameFrame - s_res[i].frame > 900) {
            /* 超时视为失败（研发耗时最长60秒=1500帧，这里给足余量） */
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
        } else if (inf.GameFrame - s_ageUpgFrame > 1800) {
            /* 升铜器耗时60秒(1500帧)，期间无 ins_ret 属正常 */
            s_ageUpgOrdered = false;
            s_ageUpgId = -1;
            s_ageUpgCdUntil = inf.GameFrame + 600;
        }
    }

    bool bronze = isBronze(inf);
    bool popOk  = (inf.Human_Num < inf.Human_MaxNum - 0.5);

    /* 进入铜器当帧复位升级锁（否则后续造人/造兵条件会被卡住） */
    if (bronze && s_ageUpgOrdered) {
        s_ageUpgOrdered = false;
        s_ageUpgId = -1;
    }

    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        const tagBuilding& b = inf.buildings[i];
        if (b.Percent < 100) continue;
        if (b.Project != ACT_NULL && b.Type != BUILDING_ARROWTOWER)
            continue;                 // 忙碌（箭塔的 Project 是它的攻击目标）

        /*---------------- 谷仓：解锁箭塔 / 箭塔强化 ----------------*/
        if (b.Type == BUILDING_GRANARY) {
            /* 解锁箭塔：建第2座塔的前置，50食物，尽早研发 */
            if (!s_res[R_TOWER_UNLOCK].done && s_res[R_TOWER_UNLOCK].id < 0 &&
                inf.GameFrame >= s_res[R_TOWER_UNLOCK].cdUntil &&
                inf.GameFrame > 100 && inf.Meat >= 50) {
                s_res[R_TOWER_UNLOCK].id =
                    BuildingAction(b.SN, BUILDING_GRANARY_ARROWTOWER);
                s_res[R_TOWER_UNLOCK].frame = inf.GameFrame;
            }
            /* 箭塔强化（铜器，120食+50石）：攻+1 射程+1 */
            else if (bronze && !s_res[R_TOWER_UPG].done &&
                     s_res[R_TOWER_UPG].id < 0 &&
                     inf.GameFrame >= s_res[R_TOWER_UPG].cdUntil &&
                     inf.Meat >= 120 && inf.Stone >= 50) {
                s_res[R_TOWER_UPG].id =
                    BuildingAction(b.SN, BUILDING_GRANARY_ARROWTOWE_UPGRADE);
                s_res[R_TOWER_UPG].frame = inf.GameFrame;
            }
        }
        /*---------------- 市场：采木科技最先，然后农田/采石/采金 ----------------*/
        else if (b.Type == BUILDING_MARKET) {
            /* 采木科技：市场一建成就研（工具时代即可，120食+75木）
             * 对应需求："市场修建后，先升级采集木头科技" */
            if (!s_res[R_WOOD].done && s_res[R_WOOD].id < 0 &&
                inf.GameFrame >= s_res[R_WOOD].cdUntil &&
                inf.Meat >= 120 && inf.Wood >= 75) {
                s_res[R_WOOD].id = BuildingAction(b.SN, BUILDING_MARKET_WOOD_UPGRADE);
                s_res[R_WOOD].frame = inf.GameFrame;
            }
            /* 驯养动物：农田>=2块后研，农田容量+75（200食+50木） */
            else if (!s_res[R_FARM].done && s_res[R_FARM].id < 0 &&
                     inf.GameFrame >= s_res[R_FARM].cdUntil &&
                     countDoneBuilding(inf, BUILDING_FARM) >= 2 &&
                     inf.Meat >= 200 && inf.Wood >= 50 &&
                     (s_res[R_TOWER_UPG].done || !bronze || inf.Meat >= 320)) {
                s_res[R_FARM].id = BuildingAction(b.SN, BUILDING_MARKET_FARM_UPGRADE);
                s_res[R_FARM].frame = inf.GameFrame;
            }
            /* 采石（100食+50石）：给箭塔强化让路 */
            else if (bronze && !s_res[R_STONE].done && s_res[R_STONE].id < 0 &&
                     inf.GameFrame >= s_res[R_STONE].cdUntil &&
                     inf.Meat >= 100 && inf.Stone >= 50 &&
                     (s_res[R_TOWER_UPG].done || inf.Stone >= 100)) {
                s_res[R_STONE].id = BuildingAction(b.SN, BUILDING_MARKET_STONE_UPGRADE);
                s_res[R_STONE].frame = inf.GameFrame;
            }
            /* 采金（120食+100木）：三种兵都吃金，优先级排在采石后 */
            else if (bronze && s_res[R_STONE].done && !s_res[R_GOLD].done &&
                     s_res[R_GOLD].id < 0 &&
                     inf.GameFrame >= s_res[R_GOLD].cdUntil &&
                     inf.Meat >= 120 && inf.Wood >= 100) {
                s_res[R_GOLD].id = BuildingAction(b.SN, BUILDING_MARKET_GOLD_UPGRADE);
                s_res[R_GOLD].frame = inf.GameFrame;
            }
        }
        /*---------------- 仓库：工具使用（近战攻+2） ----------------*/
        else if (b.Type == BUILDING_STOCK) {
            if (bronze && s_res[R_TOWER_UPG].done &&
                !s_res[R_USETOOL].done && s_res[R_USETOOL].id < 0 &&
                inf.GameFrame >= s_res[R_USETOOL].cdUntil &&
                inf.Meat >= 100) {
                s_res[R_USETOOL].id =
                    BuildingAction(b.SN, BUILDING_STOCK_UPGRADE_USETOOL);
                s_res[R_USETOOL].frame = inf.GameFrame;
            }
        }
        /*---------------- 靶场：复合弓科技 -> 只造复合弓手 ----------------*/
        else if (b.Type == BUILDING_RANGE) {
            /* 复合弓科技需铜器（180食+100木），一够就研 */
            if (bronze && !s_res[R_COMPOSITE].done && s_res[R_COMPOSITE].id < 0 &&
                inf.GameFrame >= s_res[R_COMPOSITE].cdUntil &&
                inf.Meat >= 180 && inf.Wood >= 100) {
                s_res[R_COMPOSITE].id =
                    BuildingAction(b.SN, BUILDING_RANGE_UPGRADE_COMPOSITE_BOW);
                s_res[R_COMPOSITE].frame = inf.GameFrame;
            }
            /* 造复合弓手：科技好了才造，绝不造普通弓手（省资源） */
            else if (bronze && s_res[R_COMPOSITE].done && popOk &&
                     inf.GameFrame - s_trainCdFrame >= 75 &&
                     inf.Meat >= 40 && inf.Gold >= 20) {
                BuildingAction(b.SN, BUILDING_RANGE_CREATE_COMPOSITE_BOWMAN);
                s_trainCdFrame = inf.GameFrame;
            }
        }
        /*---------------- 马厩：只造骑兵（铜器，70食+80金） ----------------*/
        else if (b.Type == BUILDING_STABLE) {
            if (bronze && popOk &&
                inf.GameFrame - s_trainCdFrame >= 75 &&
                inf.Meat >= 70 && inf.Gold >= 80) {
                BuildingAction(b.SN, BUILDING_STABLE_CREATE_CAVALRY);
                s_trainCdFrame = inf.GameFrame;
            }
        }
        /*---------------- 学院：只造方阵兵（铜器，60食+40金） ----------------*/
        else if (b.Type == BUILDING_COLLAGE) {
            if (bronze && popOk &&
                inf.GameFrame - s_trainCdFrame >= 75 &&
                inf.Meat >= 60 && inf.Gold >= 40) {
                BuildingAction(b.SN, BUILDING_COLLAGE_CREATE_HOPLITE);
                s_trainCdFrame = inf.GameFrame;
            }
        }
        /*---------------- 兵营：v6.0 不造任何兵 ----------------*/
        else if (b.Type == BUILDING_ARMYCAMP) {
            /* 兵营只是靶场/马厩的前置建筑，按需求不在此造兵 */
        }
        /*---------------- 市镇中心：升铜器 + 造村民 ----------------*/
        else if (b.Type == BUILDING_CENTER) {
            /* 最高优先级：市场+靶场建成且食物>=800 立即升铜器 */
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
            /* 造村民：按岗位序列生产，凑齐后停产（死亡才补） */
            else if (popOk && !s_ageUpgOrdered &&
                     villagerCount(inf) + s_villPending < VILL_TOTAL &&
                     inf.Meat >= VILL_FOOD_COST) {
                BuildingAction(b.SN, BUILDING_CENTER_CREATEFARMER);
                ++s_villPending;
                s_lastVillOrderFrame = inf.GameFrame;
            }
        }
    }
}

/*----------------------------------------------------------------------------
 * 4. 祭司管理
 *    优先级：转化敌军(三级目标) > 低血逃命 > 庇护期回塔 > 治疗 > 探路 > 驻守
 *    v6.5 探路目标：金矿 + 瞪羚群都要探明才收工（否则金矿近时提前收工，
 *    部分地图会一直探不到瞪羚，导致瞪羚群旁仓库建不出来）。
 *    7g 起 HumanMove 可前往未探索坐标并自动寻路，探路不再受探索限制。
 *--------------------------------------------------------------------------*/

/* 庇护窗口：波次出生前1500帧 ~ 抵达后2500帧 */
static bool inShelterWindow(int fr)
{
    return (fr >= WAVE1_SPAWN - 1500 && fr <= WAVE1_SPAWN + 2500) ||
           (fr >= WAVE2_SPAWN - 1500 && fr <= WAVE2_SPAWN + 2500) ||
           (fr >= WAVE3_SPAWN - 1500);
}

/* v6.0 转化目标三级优先级（同级取最近）：
 *   1) 正在攻击祭司的敌军（WorkObjectSN == 祭司SN）——先保命
 *   2) 方阵兵（AT_HOPLITE）——120血/17攻/5近防，最难缠
 *   3) 投石车（AT_STONE_THROWER）——对箭塔威胁最大
 *   4) 兜底：射程内最近敌军 */
static const tagArmy* pickConvertTarget(const tagInfo& inf, const tagArmy* p,
                                        double rangeBlk)
{
    double r2 = rangeBlk * s_bls * (rangeBlk * s_bls);
    const tagArmy* attacker = NULL; double dAtt = 1e18;
    const tagArmy* hoplite  = NULL; double dHop = 1e18;
    const tagArmy* thrower  = NULL; double dThr = 1e18;
    const tagArmy* nearest  = NULL; double dNea = 1e18;
    for (size_t j = 0; j < inf.enemy_armies.size(); ++j) {
        const tagArmy& e = inf.enemy_armies[j];
        double d = dist2(p->DR, p->UR, e.DR, e.UR);
        if (d > r2) continue;                       // 只考虑射程内
        if (d < dNea) { dNea = d; nearest = &e; }
        if (e.WorkObjectSN == p->SN && d < dAtt) { dAtt = d; attacker = &e; }
        if (e.Sort == AT_HOPLITE && d < dHop)      { dHop = d; hoplite = &e; }
        if (e.Sort == AT_STONE_THROWER && d < dThr){ dThr = d; thrower = &e; }
    }
    if (attacker) return attacker;
    if (hoplite)  return hoplite;
    if (thrower)  return thrower;
    return nearest;
}

/* 向目标块移动（冷却 + 仅空闲时下令，避免打断行进） */
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

bool UsrAI::priestMoveToDetail(const tagInfo& inf, const tagArmy* p,
                               double tx, double ty, int cooldown)
{
    if (p->NowState != HUMAN_STATE_IDLE) return false;
    if (inf.GameFrame - s_priestCmdFrame < cooldown) return false;
    if (dist2(p->DR, p->UR, tx, ty) < 2.5 * s_bls * (2.5 * s_bls)) return false;
    int id = HumanMove(p->SN, tx, ty);
    s_priestCmdFrame = inf.GameFrame;
    s_priestCmdId = id;
    s_priestMoveKey = -1;
    return true;
}

/* 所有已建成箭塔的质心（火力交集点），祭司驻守/躲避的默认位置 */
static void getTowerCentroid(const tagInfo& inf, double& cx, double& cy)
{
    double sumX = 0, sumY = 0;
    int cnt = 0;
    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        const tagBuilding& b = inf.buildings[i];
        if (b.Type != BUILDING_ARROWTOWER || b.Percent < 100) continue;
        sumX += blockCenter(b.BlockDR) + 0.5 * s_bls;
        sumY += blockCenter(b.BlockUR) + 0.5 * s_bls;
        ++cnt;
    }
    if (cnt > 0) { cx = sumX / cnt; cy = sumY / cnt; }
    else         { cx = blockCenter(s_tcDR); cy = blockCenter(s_tcUR); }
}

static bool priestAtCentroid(const tagInfo& inf, const tagArmy* p)
{
    double cx, cy;
    getTowerCentroid(inf, cx, cy);
    return dist2(p->DR, p->UR, cx, cy) < 3.5 * s_bls * 3.5 * s_bls;
}

/* 在箭塔周围找一块可达空地（塔中心在建筑体内，部分地图寻路进不去） */
static bool towerSideSpot(const tagInfo& inf, const tagBuilding& tw,
                          int orient, int& odr, int& our_)
{
    static const int offs[][2] = {
        { 2,  0}, {-1,  0}, { 0,  2}, { 0, -1},
        { 2,  2}, {-1,  2}, { 2, -1}, {-1, -1}
    };
    for (int i = 0; i < 8; ++i) {
        int idx = (orient + i) % 8;
        int dr = tw.BlockDR + offs[idx][0];
        int ur = tw.BlockUR + offs[idx][1];
        if (!isExplored(inf, dr, ur)) continue;
        if (inf.theMap) {
            const tagTerrain& t = (*inf.theMap)[dr][ur];
            if (t.height < 0 || t.type == MAPPATTERN_OCEAN) continue;
        }
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

    /* 0) 上一条移动指令失败 -> 拉黑该目标块 */
    if (s_priestCmdId >= 0) {
        map<int,int>::const_iterator r = inf.ins_ret.find(s_priestCmdId);
        if (r != inf.ins_ret.end()) {
            if (r->second != ACTION_SUCCESS && s_priestMoveKey >= 0)
                s_scoutBad[s_priestMoveKey] = inf.GameFrame + 3000;
            s_priestCmdId = -1;
            s_priestMoveKey = -1;
        }
    }

    double centX, centY;
    getTowerCentroid(inf, centX, centY);

    const tagArmy* en = nearestEnemy(inf, p->DR, p->UR);
    double dEn = en ? sqrt(dist2(p->DR, p->UR, en->DR, en->UR)) : 1e18;

    /* 掉血检测：60帧内掉过血 = 正在被攻击 */
    if (s_lastPriestBlood >= 0 && p->Blood < s_lastPriestBlood)
        s_priestHurtFrame = inf.GameFrame;
    s_lastPriestBlood = p->Blood;
    bool hurtNow = (inf.GameFrame - s_priestHurtFrame < 60);

    /* 1) 转化敌军——最高优先级，冷却就绪即按三级优先级转化 */
    {
        const tagArmy* cvt = pickConvertTarget(inf, p, PRIEST_CONVERT_DIS);
        if (cvt && p->ConvertCooldown == 0 &&
            inf.GameFrame - s_priestSkillFrame >= 40 &&
            (p->NowState == HUMAN_STATE_IDLE ||
             (p->NowState == HUMAN_STATE_WORKING &&
              (hurtNow || dEn < 5.0 * s_bls)))) {
            HumanAction(p->SN, cvt->SN);
            s_priestSkillFrame = inf.GameFrame;
            return;
        }
    }

    /* 2) 低血逃命：血<45% 且敌<4格 -> 远离敌人 */
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

    /* 3) 庇护期 / 敌近身：回箭塔质心（火力交集点） */
    bool needShelter = inShelterWindow(inf.GameFrame) ||
                       (en && dEn < 20.0 * s_bls);
    bool atCentroid = priestAtCentroid(inf, p);

    if (needShelter && !atCentroid) {
        /* 连续3次走不到位 -> 不再强求，就地转化或撤离 */
        if (s_shelterTries >= 3) {
            const tagArmy* cvt = pickConvertTarget(inf, p, PRIEST_CONVERT_DIS);
            if (cvt && p->ConvertCooldown == 0 &&
                inf.GameFrame - s_priestSkillFrame >= 40) {
                HumanAction(p->SN, cvt->SN);
                s_priestSkillFrame = inf.GameFrame;
                return;
            }
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
        if (p->NowState == HUMAN_STATE_IDLE &&
            inf.GameFrame - s_priestCmdFrame >= 30) {
            int id = HumanMove(p->SN, centX, centY);
            s_priestCmdFrame = inf.GameFrame;
            s_priestCmdId = id;
            s_priestMoveKey = -1;
            s_shelterSnapDR = p->DR;
            s_shelterSnapUR = p->UR;
            s_shelterMoveFrame = inf.GameFrame;
        }
        /* 卡位检测：300帧位移<0.8格 记一次失败 */
        if (s_shelterMoveFrame > 0 &&
            inf.GameFrame - s_shelterMoveFrame >= 300) {
            double lim = 0.8 * s_bls;
            if (dist2(p->DR, p->UR, s_shelterSnapDR, s_shelterSnapUR) < lim * lim)
                ++s_shelterTries;
            s_shelterMoveFrame = 0;
        }
        return;
    }
    if (!needShelter) s_shelterTries = 0;
    if (atCentroid)   s_shelterTries = 0;

    /* 4) 治疗友军：非庇护期，12格内血量比例最低且<70% */
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

    /* 5) 探路（v6.5：金矿和瞪羚群都探到才收工，探明后回塔驻守）
     *    7g 的 HumanMove 支持未探索坐标，所以直接朝最远的探索边界走；
     *    边界点走不通就拉黑换点，另设超时兜底防止一直在外浪。 */
    if (!s_goldFound || !s_gazelleFound) {
        if (s_scoutStartFrame < 0) s_scoutStartFrame = inf.GameFrame;

        /* 位移快照：500帧没动 -> 目标不可达，拉黑 */
        if (s_priestMoveKey >= 0 &&
            inf.GameFrame - s_priestSnapFrame >= 500) {
            if (s_priestSnapKey == s_priestMoveKey && s_priestSnapFrame > 0) {
                double lim = 0.8 * s_bls;
                if (dist2(p->DR, p->UR, s_priestSnapDR, s_priestSnapUR) < lim * lim) {
                    s_scoutBad[s_priestMoveKey] = inf.GameFrame + 3000;
                    s_priestMoveKey = -1;
                }
            }
            s_priestSnapDR = p->DR;
            s_priestSnapUR = p->UR;
            s_priestSnapFrame = inf.GameFrame;
            s_priestSnapKey = s_priestMoveKey;
        }
        if (p->NowState == HUMAN_STATE_WALKING) return;

        /* 超时兜底：探路超过 9000 帧还没探全就收工回塔 */
        if (inf.GameFrame - s_scoutStartFrame > 9000) {
            s_goldFound = true;
            s_gazelleFound = true;
        } else {
            /* 选最远的探索边界（往外推，最大化开图效率） */
            int fdr = -1, fur = -1;
            double bd = -1;
            for (size_t k = 0; k < s_frontier.size(); ++k) {
                int kx = s_frontier[k].first, ky = s_frontier[k].second;
                int key = bkey(kx, ky);
                map<int,int>::const_iterator sb = s_scoutBad.find(key);
                if (sb != s_scoutBad.end() && inf.GameFrame < sb->second) continue;
                double tx = blockCenter(kx), ty = blockCenter(ky);
                double d = dist2(p->DR, p->UR, tx, ty);
                if (d < 3.0 * s_bls * 3.0 * s_bls) continue;   // 太近的不算
                if (d > bd) { bd = d; fdr = kx; fur = ky; }
            }
            if (fdr >= 0) {
                priestMoveTo(inf, p, fdr, fur, 60);
                return;
            }
        }
    }

    /* 6) 默认驻守：箭塔质心 */
    if (!priestAtCentroid(inf, p) && p->NowState == HUMAN_STATE_IDLE &&
        inf.GameFrame - s_priestCmdFrame >= 120) {
        int id = HumanMove(p->SN, centX, centY);
        s_priestCmdFrame = inf.GameFrame;
        s_priestCmdId = id;
        s_priestMoveKey = -1;
    }
}

/*----------------------------------------------------------------------------
 * 5. 箭塔：优先打"正在攻击祭司"的敌军，其次投石车，最后射程内最近敌
 *--------------------------------------------------------------------------*/
void UsrAI::manageTowers(const tagInfo& inf)
{
    const tagArmy* priest = findPriest(inf);
    int priestSN = priest ? priest->SN : -1;

    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        const tagBuilding& b = inf.buildings[i];
        if (b.Type != BUILDING_ARROWTOWER || b.Percent < 100) continue;
        if (b.Project >= 0) continue;              // 已有攻击目标

        int last = -1000;
        map<int,int>::iterator it = s_towerCmdFrame.find(b.SN);
        if (it != s_towerCmdFrame.end()) last = it->second;
        if (inf.GameFrame - last < 10) continue;

        double tx = blockCenter(b.BlockDR), ty = blockCenter(b.BlockUR);
        double range = 8.0 * s_bls;                // 射程7格(强化8格)，留余量
        double range2 = range * range;

        const tagArmy* target = NULL;
        double bestD = 1e18;

        /* 优先级1：正在攻击祭司的敌军 */
        if (priestSN >= 0) {
            for (size_t j = 0; j < inf.enemy_armies.size(); ++j) {
                const tagArmy& e = inf.enemy_armies[j];
                if (e.WorkObjectSN != priestSN) continue;
                double d = dist2(tx, ty, e.DR, e.UR);
                if (d < range2 && d < bestD) { bestD = d; target = &e; }
            }
        }
        /* 优先级2：投石车（射程10格>塔，能在塔射程外拆塔） */
        if (!target) {
            for (size_t j = 0; j < inf.enemy_armies.size(); ++j) {
                const tagArmy& e = inf.enemy_armies[j];
                if (e.Sort != AT_STONE_THROWER) continue;
                double d = dist2(tx, ty, e.DR, e.UR);
                if (d < range2 && d < bestD) { bestD = d; target = &e; }
            }
        }
        /* 优先级3：射程内最近敌军 */
        if (!target) {
            for (size_t j = 0; j < inf.enemy_armies.size(); ++j) {
                const tagArmy& e = inf.enemy_armies[j];
                double d = dist2(tx, ty, e.DR, e.UR);
                if (d < range2 && d < bestD) { bestD = d; target = &e; }
            }
        }

        if (target) {
            HumanAction(b.SN, target->SN);
            s_towerCmdFrame[b.SN] = inf.GameFrame;
        }
    }
}

/*----------------------------------------------------------------------------
 * 6. 军队：最高优先级 = 正在攻击祭司的敌军；其次投石车；
 *    再次基地警戒圈(28格)内最近敌；无敌情时在塔群附近集结
 *--------------------------------------------------------------------------*/
void UsrAI::manageArmies(const tagInfo& inf)
{
    if (s_tcDR < 0) return;

    /* 集结点：箭塔质心附近 */
    double gx, gy;
    getTowerCentroid(inf, gx, gy);
    double holdR = 3.0 * s_bls;
    double tcx = blockCenter(s_tcDR), tcy = blockCenter(s_tcUR);
    double engageR = 28.0 * s_bls;

    const tagArmy* priest = findPriest(inf);
    int priestSN = priest ? priest->SN : -1;

    for (size_t i = 0; i < inf.armies.size(); ++i) {
        const tagArmy& a = inf.armies[i];
        if (a.Sort == AT_PRIEST) continue;         // 祭司由 managePriest 指挥

        if (!inf.enemy_armies.empty()) {
            if (a.NowState != HUMAN_STATE_IDLE &&
                a.NowState != HUMAN_STATE_WALKING) continue;

            int last = -1000;
            map<int,int>::iterator it = s_armyCmdFrame.find(a.SN);
            if (it != s_armyCmdFrame.end()) last = it->second;
            if (inf.GameFrame - last < 15) continue;

            const tagArmy* target = NULL;
            double bd = 1e18;

            /* 优先级1：正在攻击祭司的敌军 */
            if (priestSN >= 0) {
                for (size_t j = 0; j < inf.enemy_armies.size(); ++j) {
                    const tagArmy& e = inf.enemy_armies[j];
                    if (e.WorkObjectSN != priestSN) continue;
                    double dd = dist2(a.DR, a.UR, e.DR, e.UR);
                    if (dd < bd) { bd = dd; target = &e; }
                }
            }
            /* 优先级2：警戒圈内的投石车 */
            if (!target) {
                for (size_t j = 0; j < inf.enemy_armies.size(); ++j) {
                    const tagArmy& e = inf.enemy_armies[j];
                    if (e.Sort != AT_STONE_THROWER) continue;
                    if (dist2(tcx, tcy, e.DR, e.UR) > engageR * engageR) continue;
                    double dd = dist2(a.DR, a.UR, e.DR, e.UR);
                    if (dd < bd) { bd = dd; target = &e; }
                }
            }
            /* 优先级3：警戒圈内最近敌军 */
            if (!target) {
                for (size_t j = 0; j < inf.enemy_armies.size(); ++j) {
                    const tagArmy& e = inf.enemy_armies[j];
                    if (dist2(tcx, tcy, e.DR, e.UR) > engageR * engageR) continue;
                    double dd = dist2(a.DR, a.UR, e.DR, e.UR);
                    if (dd < bd) { bd = dd; target = &e; }
                }
            }
            if (target) {
                HumanAction(a.SN, target->SN);
                s_armyCmdFrame[a.SN] = inf.GameFrame;
            }
        }
        else if (a.NowState == HUMAN_STATE_IDLE &&
                 dist2(a.DR, a.UR, gx, gy) > holdR * holdR) {
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
 * 主入口：每帧调用
 *==========================================================================*/
void UsrAI::processData()
{
    info = getInfo();
    const tagInfo& inf = info;

    /*---------------- 首帧初始化 ----------------*/
    if (s_tcDR < 0) {
        s_bls = BLOCKSIDELENGTH;
        for (int i = 0; i < R_NUM; ++i) {
            s_res[i].id = -1; s_res[i].frame = 0;
            s_res[i].cdUntil = 0; s_res[i].done = false;
        }
        s_pend.id = -1; s_pend.type = -1; s_pend.dr = -1; s_pend.ur = -1;
        s_pend.frame = 0; s_pend.builderSN = -1;
        s_pendStock.id = -1; s_pendStock.type = -1;
        s_pendStock.dr = -1; s_pendStock.ur = -1;
        s_pendStock.frame = 0; s_pendStock.builderSN = -1;
        s_ageUpgId = -1;
        s_ageUpgOrdered = false;
        s_priestCmdId = -1;
        s_priestMoveKey = -1;
        s_priestCmdFrame = -999;
        s_trainCdFrame = 0;
        s_villPending = 0;

        /* 记录各类初始建筑位置（随机地图+随机旋转，必须实读） */
        const tagBuilding* tc = NULL;
        const tagBuilding* tw0 = NULL;
        const tagBuilding* hm0 = NULL;
        const tagBuilding* st0 = NULL;
        const tagBuilding* gr0 = NULL;
        for (size_t i = 0; i < inf.buildings.size(); ++i) {
            const tagBuilding& b = inf.buildings[i];
            if (b.Type == BUILDING_CENTER      && !tc)  tc  = &b;
            if (b.Type == BUILDING_ARROWTOWER  && !tw0) tw0 = &b;
            if (b.Type == BUILDING_HOME        && !hm0) hm0 = &b;
            if (b.Type == BUILDING_STOCK       && !st0) st0 = &b;
            if (b.Type == BUILDING_GRANARY     && !gr0) gr0 = &b;
        }
        if (tc)  { s_tcDR = tc->BlockDR;  s_tcUR = tc->BlockUR; }
        else     { s_tcDR = 22; s_tcUR = 20; }
        if (tw0) { s_twDR = tw0->BlockDR; s_twUR = tw0->BlockUR; }
        if (hm0) { s_homeDR = hm0->BlockDR; s_homeUR = hm0->BlockUR; }
        if (st0) { s_stockDR = st0->BlockDR; s_stockUR = st0->BlockUR; }
        if (gr0) { s_granaryDR = gr0->BlockDR; s_granaryUR = gr0->BlockUR; }
        s_lastFarmerCnt = villagerCount(inf);
    }

    /*---------------- 探索信息 ----------------*/
    updateExplored(inf);

    /*---------------- 金矿/瞪羚探明检测（供祭司收工 & 建旁仓库） ----------------*/
    if (!s_goldFound) {
        for (size_t i = 0; i < inf.resources.size(); ++i) {
            if (inf.resources[i].Type == RESOURCE_GOLD &&
                inf.resources[i].Cnt > 0) { s_goldFound = true; break; }
        }
    }
    if (!s_gazelleFound) {
        for (size_t i = 0; i < inf.resources.size(); ++i) {
            if (inf.resources[i].Type == RESOURCE_GAZELLE &&
                inf.resources[i].Cnt > 0) { s_gazelleFound = true; break; }
        }
    }

    /*---------------- 岗位分配 ----------------*/
    countJobs(inf);
    if (!s_initJobsDone) {
        assignInitialJobs(inf);      // 初始8人：浆果3/建造1/采木3/采石1
        s_initJobsDone = true;
        countJobs(inf);
    }
    assignSeqJobs(inf);              // 新村民按序列分配岗位
    cleanJobs(inf);                  // 清理死者并补员
    countJobs(inf);                  // 重新统计（供造人判断）

    /*---------------- 村民生产队列核算 ----------------*/
    int nowFarmers = villagerCount(inf);
    if (nowFarmers > s_lastFarmerCnt) {
        s_villPending -= (nowFarmers - s_lastFarmerCnt);
        if (s_villPending < 0) s_villPending = 0;
    }
    if (s_villPending > 0 && inf.GameFrame - s_lastVillOrderFrame > 1200)
        s_villPending = 0;           // 指令被拒时防卡死
    s_lastFarmerCnt = nowFarmers;

    /*---------------- 各模块 ----------------*/
    manageBuild(inf);            // 建造流水线 + 农田 + 定点仓库 + 续建
    manageBuildingActions(inf);  // 科技 / 造村民 / 三种兵 / 升时代
    manageFarmers(inf);          // 村民按岗位干活
    managePriest(inf);           // 祭司：转化 / 治疗 / 探金矿+瞪羚 / 驻守
    manageTowers(inf);           // 箭塔
    manageArmies(inf);           // 军队

    /*---------------- 调试输出（每600帧=24秒） ----------------*/
    if (inf.GameFrame % 600 == 0) {
        const tagArmy* priest = findPriest(inf);
        DebugText(QString(
            "[AIv6] f=%1 meat=%2 wood=%3 stone=%4 gold=%5 pop=%6/%7 civ=%8 "
            "vill=%9 army=%10 tw=%11 farm=%12 home=%13 step=%14 goldFound=%15 pHp=%16 "
            "gazFound=%17 jobs[B%18 W%19 S%20 H%21 G%22 F%23 C%24]")
            .arg(inf.GameFrame).arg(inf.Meat).arg(inf.Wood).arg(inf.Stone)
            .arg(inf.Gold)
            .arg(inf.Human_Num).arg(inf.Human_MaxNum)
            .arg(inf.civilizationStage)
            .arg(nowFarmers)
            .arg(armyCountNonPriest(inf))
            .arg(countAnyBuilding(inf, BUILDING_ARROWTOWER))
            .arg(countAnyBuilding(inf, BUILDING_FARM))
            .arg(countAnyBuilding(inf, BUILDING_HOME))
            .arg(s_buildStep)
            .arg(s_goldFound ? 1 : 0)
            .arg(priest ? priest->Blood : 0)
            .arg(s_gazelleFound ? 1 : 0)
            .arg(s_cntB).arg(s_cntW).arg(s_cntS)
            .arg(s_cntH).arg(s_cntG).arg(s_cntF).arg(s_cntC));
    }
}
