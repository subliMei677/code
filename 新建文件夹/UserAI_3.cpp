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
 * AI v3 —— 目标：及格线强化（存活 + 升级铜器时代），为完整胜利版打底
 *
 * 波次节奏（地图预置）：
 *   第一波 ~6000帧 出生（2斧头兵+1弓箭手），行军约1300帧后抵达
 *   第二波 ~13500帧 出生（含方阵兵/阔剑兵/复合弓兵/战车弓兵）
 *   第三波 ~21000帧 出生（铜器部队+投石车）
 *
 * v3 总体时间线：
 *   [0, 4500]   经济起步：研发箭塔解锁 → 3座箭塔成簇（初始300石+采石150）
 *               市场 → 靶场（升铜器前置）；村民持续生产；祭司在基地近环探路
 *   [4500, 7800] 庇护窗口1：祭司回塔簇下躲避，靠3箭塔扛过第一波（不造兵）
 *   [7800, 11800] 恢复期：补农田（目标8块）、囤800食物、继续造村民；
 *               市场研发木材加工；祭司第二轮探路
 *   [~10000]    市场+靶场就绪且食物≥800 → 升级铜器（60秒）
 *   [11800, 16000] 庇护窗口2：箭塔强化科技（攻+1射程+1）+ 兵营练兵
 *               （棍棒兵+弓箭手）扛过第二波
 *   [19800, ∞)  庇护窗口3：长期防守，铜器科技（驯养/兵营升级/阔剑兵）
 *
 * v3 修复的 5 个问题（相对 v2）：
 *   1. 村民太少 → 持续生产（目标 8+帧/450，上限36），不再限制开局窗口
 *   2. 祭司探路不动+指令刷屏 → 根因是 v2 探路分支在 IDLE 时每帧重发；
 *      v3 改为：90帧统一冷却 + ins_ret 失败立即拉黑路点 +
 *      600帧无位移拉黑路点 + 狮子规避
 *   3. 箭塔太远 → 塔簇偏移表（TC东南3~7格，间距≥3格互不重叠）；
 *      内核 DIS_BUILD_ARROWTOWER(5) 仅是配置值，建造校验未使用
 *   4. 木材太慢 → 伐木配额6人 + 市场木材加工（采集率0.02→0.22，11倍）
 *   5. 多人采同一农田 → 用 WorkObjectSN 统计实时占用：农田1人/块，
 *      树/石/金 2~3人/个
 *
 * 引擎机制备忘（源码核实，v2 沿用）：
 *   - 采集指令下达后内核自动"采集->上交->返回"循环，无需每帧重发
 *   - 上交规则：市镇中心收全部；仓库收木/石/金/浆果/猎物；谷仓只收农田食物
 *   - 指令按单位去重；每帧最多处理"建筑数+人口数"条指令
 *   - 250帧无进展的行动会被内核强制中断回空闲
 *   - 箭塔 Project：-1空闲 / >=0 当前攻击目标（重复下令会重置攻击）
 *   - 建筑占地：房屋/箭塔 2×2，农田/市场/靶场/兵营 3×3（块）
 *   - 建造失败码：未探索(UNEXPLORE)不应消耗候选位，稍后重试
 *==========================================================================*/
#include <map>
#include <vector>
#include <cmath>

tagInfo info;

/*----------------------------------------------------------------------------
 * 全局策略状态
 *--------------------------------------------------------------------------*/
static double s_bls = 35.777;             // 块边长 BLOCKSIDELENGTH（首帧读取）
static int    s_tcDR = -1, s_tcUR = -1;   // 市镇中心块坐标（建造/集结参照）

/*--- 科技研发状态机（一次性科技，经 ins_ret 确认） ---*/
struct ResearchState { int id; int frame; int cdUntil; bool done; };
enum { R_TOWER_UNLOCK = 0,   // 谷仓：解锁箭塔（50食/10秒）
       R_TOWER_UPG,          // 谷仓：箭塔强化 攻+1 射程+1（120食+50石/40秒）
       R_WOOD,               // 市场：木材加工 采集率x11（120食+75木/40秒）
       R_FARM,               // 市场：驯养动物 农田+75食（200食+50木）
       R_CLUB,               // 兵营：升级棍棒兵（100食/40秒，铜器）
       R_BROAD,              // 兵营：阔剑兵科技（140食+50金/40秒，铜器）
       R_NUM };
static ResearchState s_res[R_NUM];        // 首帧统一初始化

/*--- 升级时代指令跟踪 ---*/
static bool s_ageUpgOrdered = false;      // 已下达升铜器指令（解锁练兵）
static int  s_ageUpgId = -1;
static int  s_ageUpgFrame = 0;
static int  s_ageUpgCdUntil = 0;          // 失败重试冷却

/*--- 建造管理：两个在途槽位（塔与房屋/农田等可并行施工） ---*/
struct PendBuild { int id; int type; int posIdx; int frame; int builderSN; };
static PendBuild s_pend[2] = { { -1, -1, -1, 0, -1 },
                               { -1, -1, -1, 0, -1 } };
static map<int, int> s_buildRetryAfter;   // 建筑类型 -> 重试截止帧（未探索等）

static int s_towerIdx = 0, s_farmIdx = 0, s_houseIdx = 0;
static int s_marketIdx = 0, s_rangeIdx = 0, s_campIdx = 0;

/*--- 村民状态 ---*/
static map<int, char> s_farmerRole;       // 村民SN -> 'F'食/'W'木/'S'石/'G'金
static map<int, int>  s_lastFleeFrame;    // SN -> 上次逃跑帧
static map<int, int>  s_farmerCmdFrame;   // SN -> 上次下令帧
static map<int, int>  s_farmerCmdId;      // SN -> 上次下令指令id（查ins_ret）
static map<int, int>  s_farmerCmdTarget;  // SN -> 上次下令目标SN
static map<int, char> s_farmerCmdKind;    // 'G'采集/'D'上交/'M'移动
static map<int, int>  s_farmerStuck;      // SN -> 连续快速回空闲次数
static map<int, int>  s_targetBadUntil;   // 目标SN -> 拉黑截止帧

/*--- 祭司探路状态 ---*/
static set<int> s_exploredKey;            // 已探索块集合（key=DR*1000+UR）
static int  s_scoutIdx = 0;               // 当前探路路点下标
static bool s_wpVisited[32];              // 路点已到达（静态零初始化）
static bool s_wpBad[32];                  // 路点不可达被拉黑
static int  s_priestCmdFrame = -999;      // 祭司上次下令帧（统一冷却）
static int  s_priestCmdId = -1;           // 上次下令指令id（查ins_ret）
static int  s_priestCmdWp = -1;           // 下令时前往的路点（失败时拉黑用）
static double s_priestSnapDR = 0, s_priestSnapUR = 0;   // 位移快照（无位移检测）
static int  s_priestSnapFrame = 0;        // 快照帧号
static int  s_priestSnapWp = -1;          // 快照时的路点下标

/*--- 军队/箭塔指令冷却 ---*/
static map<int, int> s_armyCmdFrame;
static map<int, int> s_towerCmdFrame;
static int s_trainCdFrame = 0;            // 练兵指令冷却（防失败刷屏）

/*----------------------------------------------------------------------------
 * 位置偏移表（相对市镇中心的块坐标；已核对互不重叠：
 *   房屋/箭塔占地2x2，农田/市场/靶场/兵营占地3x3，
 *   且避开开局建筑：TC(22,20) 箭塔(20,27) 房屋(22,16)(24,16)
 *   仓库(9,16) 谷仓(18,13)；敌方来向为东南，箭塔簇置于TC东南侧）
 *--------------------------------------------------------------------------*/
/* 箭塔簇：3~9格范围紧凑排布，是祭司的庇护所 */
static const int TOWER_OFFSETS[][2] = {
    { 3,  3}, { 6,  1}, { 1,  6}, { 7,  5}, { 5,  7}, { 9,  2}, { 2,  9}
};
static const int TOWER_NUM =
    (int)(sizeof(TOWER_OFFSETS) / sizeof(TOWER_OFFSETS[0]));

/* 农田：置于基地西北（谷仓/仓库一侧，缩短上交路途） */
static const int FARM_OFFSETS[][2] = {
    { -8,  -2}, { -8,   2}, {-12,  -1}, {-13,  -7},
    { -5, -10}, { -2, -10}, {  1, -10}, {  4,  -8},
    { -7,   7}, { -7,  10}
};
static const int FARM_NUM =
    (int)(sizeof(FARM_OFFSETS) / sizeof(FARM_OFFSETS[0]));

/* 房屋：环绕基地外圈 */
static const int HOUSE_OFFSETS[][2] = {
    { -5,   5}, {  5,  -5}, { -5,  -3}, {  3,  -6}, { -3,  -6},
    {-12,   3}, { 12,  -3}, { -9,   8}, {  8,  -9}, {  7,  13},
    { 13,   8}, {  0,  12}, { 12,   0}, { -8,  -6}, {  6,  -8}
};
static const int HOUSE_NUM =
    (int)(sizeof(HOUSE_OFFSETS) / sizeof(HOUSE_OFFSETS[0]));

/* 市场/靶场/兵营：东南外圈（靶场与兵营在塔簇掩护之下） */
static const int MARKET_OFFSETS[][2] = { { 8,  8}, {12, 12}, {14,  6} };
static const int RANGE_OFFSETS[][2]  = { { 4, 11}, {11, 14}, {14, 11} };
static const int CAMP_OFFSETS[][2]   = { {11,  5}, { 5, 14}, {14,  2} };
static const int MARKET_NUM = (int)(sizeof(MARKET_OFFSETS) / sizeof(MARKET_OFFSETS[0]));
static const int RANGE_NUM  = (int)(sizeof(RANGE_OFFSETS)  / sizeof(RANGE_OFFSETS[0]));
static const int CAMP_NUM   = (int)(sizeof(CAMP_OFFSETS)   / sizeof(CAMP_OFFSETS[0]));

/* 祭司探路路点（绝对块坐标，由近及远；敌方基地在东南(86,86)，
 * 先探北/西安全方向，逐步向中央推进；单点不可达会自动拉黑） */
static const int SCOUT_WAYPOINTS[][2] = {
    {30, 10}, {10, 30}, {40, 18}, {18, 40},          // 基地近环
    {35, 35}, {50, 25}, {25, 50},                    // 中环
    {60, 20}, {20, 60}, {55, 40}, {40, 55},          // 中远环
    {65, 50}, {50, 65}, {60, 60}, {70, 35}, {35, 70} // 远环（为进攻探路）
};
static const int SCOUT_NUM =
    (int)(sizeof(SCOUT_WAYPOINTS) / sizeof(SCOUT_WAYPOINTS[0]));

/*----------------------------------------------------------------------------
 * 通用小工具
 *--------------------------------------------------------------------------*/
static double dist2(double dr1, double ur1, double dr2, double ur2)
{
    double a = dr1 - dr2, b = ur1 - ur2;
    return a * a + b * b;
}

static double blockCenter(int b) { return (b + 0.5) * s_bls; }

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

static int countAnyBuilding(const tagInfo& inf, int type)   // 含在建
{
    int n = 0;
    for (size_t i = 0; i < inf.buildings.size(); ++i)
        if (inf.buildings[i].Type == type) ++n;
    return n;
}

static int countDoneBuilding(const tagInfo& inf, int type)  // 仅已建成
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

/* 远程单位数（用于弓箭手配额） */
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

/* 近战单位数（不含祭司和远程） */
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
    map<int, int>::const_iterator it = s_targetBadUntil.find(sn);
    return it != s_targetBadUntil.end() && inf.GameFrame < it->second;
}

static void updateExplored(const tagInfo& inf)
{
    for (size_t i = 0; i < inf.exploredUpdate.size(); ++i)
        s_exploredKey.insert(inf.exploredUpdate[i].x * 1000 +
                             inf.exploredUpdate[i].y);
}


static void noteFarmerCmd(int sn, int id, int target, char kind, int frame)
{
    s_farmerCmdId[sn]     = id;
    s_farmerCmdTarget[sn] = target;
    s_farmerCmdKind[sn]   = kind;
    s_farmerCmdFrame[sn]  = frame;
}

/* 清理已阵亡/消失村民的状态记录（防止统计污染） */
static void cleanFarmerMaps(const tagInfo& inf)
{
    set<int> alive;
    for (size_t i = 0; i < inf.farmers.size(); ++i)
        alive.insert(inf.farmers[i].SN);

    vector<int> dead;
    for (map<int, char>::iterator it = s_farmerRole.begin();
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
 * 村民分工（v3：动态配额制）
 *   石头：3座箭塔+箭塔强化科技的需求缺口决定（0~4人）
 *   金矿：铜器后 2 人（阔剑兵科技需要）
 *   木材：木材加工研发前 6 人，研发后 4 人（速率x11）
 *   食物：其余全部（下限6人）
 *--------------------------------------------------------------------------*/
static char getRoleSN(int sn)
{
    map<int, char>::const_iterator it = s_farmerRole.find(sn);
    return (it != s_farmerRole.end()) ? it->second : 'F';
}

static char pickRole(const tagInfo& inf)
{
    bool bronze = (inf.civilizationStage >= CIVILIZATION_BRONZEAGE);

    // 石头需求：还差的箭塔数 x 150 + 箭塔强化50 - 当前库存
    int towersBuilt = countAnyBuilding(inf, BUILDING_ARROWTOWER);
    int stoneNeed = 150 * (3 - towersBuilt);
    if (towersBuilt >= 3 && !s_res[R_TOWER_UPG].done) stoneNeed += 50;
    stoneNeed -= inf.Stone;
    if (stoneNeed < 0) stoneNeed = 0;

    int qS = (stoneNeed > 200) ? 4 : (stoneNeed > 0 ? 2 : 0);
    int qG = (bronze && inf.Gold < 250) ? 2 : 0;
    int qW = s_res[R_WOOD].done ? 4 : 6;
    int qF = 6;

    int cF = 0, cW = 0, cS = 0, cG = 0;
    for (size_t i = 0; i < inf.farmers.size(); ++i) {
        char r = getRoleSN(inf.farmers[i].SN);
        if (r == 'F') ++cF;
        else if (r == 'W') ++cW;
        else if (r == 'S') ++cS;
        else if (r == 'G') ++cG;
    }

    int dF = qF - cF, dW = qW - cW, dS = qS - cS, dG = qG - cG;
    char best = 'F';
    int bd = dF;
    if (dS > bd) { bd = dS; best = 'S'; }
    if (dG > bd) { bd = dG; best = 'G'; }
    if (dW > bd) { bd = dW; best = 'W'; }
    return best;
}

/* 统计某资源/农田上正在工作的村民数（v3：解决多人采同一农田问题）
 * 依据内核字段 WorkObjectSN（正在采集）+ 我方指令跟踪（在途前往） */
static int workersOnTarget(const tagInfo& inf, int targetSN, int selfSN)
{
    int n = 0;
    for (size_t i = 0; i < inf.farmers.size(); ++i) {
        const tagFarmer& f = inf.farmers[i];
        if (f.SN == selfSN) continue;
        if (f.NowState == HUMAN_STATE_IDLE) continue;
        if (f.WorkObjectSN == targetSN) { ++n; continue; }
        map<int, int>::const_iterator it = s_farmerCmdTarget.find(f.SN);
        if (it != s_farmerCmdTarget.end() && it->second == targetSN) ++n;
    }
    return n;
}

/* 各类资源的同时采集人数上限 */
static int resCap(int resType)
{
    switch (resType) {
    case RESOURCE_TREE:   return 2;   // 一棵树最多2人
    case RESOURCE_BUSH:   return 3;   // 一丛浆果最多3人
    case RESOURCE_STONE:  return 3;   // 一处石矿最多3人
    case RESOURCE_GOLD:   return 2;
    case RESOURCE_GAZELLE:
    case RESOURCE_ELEPHANT: return 2;
    default:              return 3;
    }
}

/* 按分工找最近且未满员的资源；农田兜底（1人1田） */
static int nearestResourceSN(const tagInfo& inf, double dr, double ur,
                             char role, int excludeSN, int selfSN)
{
    int sn = -1;
    double bd = 1e18;
    for (size_t i = 0; i < inf.resources.size(); ++i) {
        const tagResource& r = inf.resources[i];
        if (r.Cnt <= 0) continue;
        if (r.SN == excludeSN) continue;
        if (targetBad(inf, r.SN)) continue;
        bool ok = false;
        if (role == 'F')
            ok = (r.Type == RESOURCE_BUSH || r.Type == RESOURCE_GAZELLE ||
                  r.Type == RESOURCE_ELEPHANT);
        else if (role == 'W')
            ok = (r.Type == RESOURCE_TREE);
        else if (role == 'S')
            ok = (r.Type == RESOURCE_STONE);
        else if (role == 'G')
            ok = (r.Type == RESOURCE_GOLD);
        if (!ok) continue;
        if (workersOnTarget(inf, r.SN, selfSN) >= resCap((int)r.Type)) continue;
        double d = dist2(dr, ur, r.DR, r.UR);
        if (d < bd) { bd = d; sn = r.SN; }
    }
    if (sn < 0 && role == 'F') { // 农田兜底：一块田只派1人
        for (size_t i = 0; i < inf.buildings.size(); ++i) {
            const tagBuilding& b = inf.buildings[i];
            if (b.Type != BUILDING_FARM || b.Percent < 100 || b.Cnt <= 0) continue;
            if (b.SN == excludeSN || targetBad(inf, b.SN)) continue;
            if (workersOnTarget(inf, b.SN, selfSN) >= 1) continue;
            double d = dist2(dr, ur, blockCenter(b.BlockDR), blockCenter(b.BlockUR));
            if (d < bd) { bd = d; sn = b.SN; }
        }
    }
    return sn;
}

/*----------------------------------------------------------------------------
 * 建造表工具
 *--------------------------------------------------------------------------*/
static int& typeCursor(int type)
{
    if (type == BUILDING_ARROWTOWER) return s_towerIdx;
    if (type == BUILDING_FARM)       return s_farmIdx;
    if (type == BUILDING_HOME)       return s_houseIdx;
    if (type == BUILDING_MARKET)     return s_marketIdx;
    if (type == BUILDING_RANGE)      return s_rangeIdx;
    return s_campIdx;
}

static void getBuildTable(int type, const int (*&offs)[2], int& num)
{
    switch (type) {
    case BUILDING_ARROWTOWER: offs = TOWER_OFFSETS; num = TOWER_NUM; break;
    case BUILDING_FARM:       offs = FARM_OFFSETS;  num = FARM_NUM;  break;
    case BUILDING_HOME:       offs = HOUSE_OFFSETS; num = HOUSE_NUM; break;
    case BUILDING_MARKET:     offs = MARKET_OFFSETS;num = MARKET_NUM;break;
    case BUILDING_RANGE:      offs = RANGE_OFFSETS; num = RANGE_NUM; break;
    default:                  offs = CAMP_OFFSETS;  num = CAMP_NUM;  break;
    }
}

static bool buildRetryOk(const tagInfo& inf, int type)
{
    map<int, int>::const_iterator it = s_buildRetryAfter.find(type);
    return it == s_buildRetryAfter.end() || inf.GameFrame >= it->second;
}

/*----------------------------------------------------------------------------
 * 1. 建造管理（v3：双在途槽位，箭塔与房屋/农田可并行施工）
 *    优先级：房屋(人口) > 箭塔x3 > 市场 > 靶场 > 农田x8 > 兵营(第一波后)
 *    失败处理：未探索→600帧后原位重试；其他失败/成功→候选位顺延
 *--------------------------------------------------------------------------*/
void UsrAI::manageBuild(const tagInfo& inf)
{
    // 1) 解决在途建造指令
    for (int k = 0; k < 2; ++k) {
        if (s_pend[k].id < 0) continue;
        map<int, int>::const_iterator it = inf.ins_ret.find(s_pend[k].id);
        int res;
        if (it != inf.ins_ret.end()) res = it->second;
        else if (inf.GameFrame - s_pend[k].frame > 600) res = -1;  // 超时视为失败
        else continue;

        if (res == ACTION_INVALID_HUMANBUILD_UNEXPLORE) {
            // 位置未探索：不消耗候选位，600帧后重试
            s_buildRetryAfter[s_pend[k].type] = inf.GameFrame + 600;
        } else {
            // 成功（位置已被占用）或真失败（位置不可用）：候选位顺延
            int& cur = typeCursor(s_pend[k].type);
            if (cur <= s_pend[k].posIdx) cur = s_pend[k].posIdx + 1;
        }
        s_pend[k].id = -1;
        s_pend[k].type = -1;
        s_pend[k].builderSN = -1;
    }

    // 2) 找空闲槽位
    int slot = -1;
    for (int k = 0; k < 2; ++k)
        if (s_pend[k].id < 0) { slot = k; break; }
    if (slot < 0 || s_tcDR < 0) return;

    // 3) 优先级链（跳过已有在途/冷却中的类型）
    bool typePend[16];
    for (int t = 0; t < 16; ++t) typePend[t] = false;
    for (int k = 0; k < 2; ++k)
        if (s_pend[k].id >= 0 && s_pend[k].type >= 0 && s_pend[k].type < 16)
            typePend[s_pend[k].type] = true;

    int want = -1;
    if (!typePend[BUILDING_HOME] && buildRetryOk(inf, BUILDING_HOME) &&
        inf.Human_Num >= inf.Human_MaxNum - 1 && inf.Wood >= 30)
        want = BUILDING_HOME;                                   // 房屋（人口将满）
    else if (!typePend[BUILDING_ARROWTOWER] &&
             buildRetryOk(inf, BUILDING_ARROWTOWER) &&
             countAnyBuilding(inf, BUILDING_ARROWTOWER) < 3 &&
             s_res[R_TOWER_UNLOCK].done && inf.Stone >= 150)
        want = BUILDING_ARROWTOWER;                             // 第3座箭塔前优先
    else if (!typePend[BUILDING_MARKET] && buildRetryOk(inf, BUILDING_MARKET) &&
             countAnyBuilding(inf, BUILDING_MARKET) == 0 && inf.Wood >= 150)
        want = BUILDING_MARKET;                                 // 升铜器前置1
    else if (!typePend[BUILDING_RANGE] && buildRetryOk(inf, BUILDING_RANGE) &&
             countAnyBuilding(inf, BUILDING_RANGE) == 0 &&
             countAnyBuilding(inf, BUILDING_MARKET) > 0 && inf.Wood >= 150)
        want = BUILDING_RANGE;                                  // 升铜器前置2
    else if (!typePend[BUILDING_FARM] && buildRetryOk(inf, BUILDING_FARM) &&
             countAnyBuilding(inf, BUILDING_FARM) < 8 &&
             countAnyBuilding(inf, BUILDING_MARKET) > 0 &&
             inf.Wood >= 75 && inf.GameFrame > 2500)
        want = BUILDING_FARM;                                   // 农田（目标8块）
    else if (!typePend[BUILDING_ARMYCAMP] && buildRetryOk(inf, BUILDING_ARMYCAMP) &&
             countAnyBuilding(inf, BUILDING_ARMYCAMP) == 0 &&
             inf.GameFrame > 7500 && inf.Wood >= 125)
        want = BUILDING_ARMYCAMP;                               // 兵营（第一波后）
    if (want < 0) return;

    // 4) 取候选位置
    const int (*offs)[2];
    int num;
    getBuildTable(want, offs, num);
    int& cur = typeCursor(want);
    if (cur >= num) return;                    // 该类型候选位置用尽

    int dr = s_tcDR + offs[cur][0];
    int ur = s_tcUR + offs[cur][1];
    if (dr < 1) dr = 1;
    if (dr > MAP_L - 4) dr = MAP_L - 4;
    if (ur < 1) ur = 1;
    if (ur > MAP_U - 4) ur = MAP_U - 4;

    // 5) 找最近的空闲村民当建造者
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
    s_pend[slot].posIdx = cur;
    s_pend[slot].frame = inf.GameFrame;
    s_pend[slot].builderSN = builder->SN;
    noteFarmerCmd(builder->SN, id, -1, 'M', inf.GameFrame);
}

/*----------------------------------------------------------------------------
 * 2. 建筑行动：科技研发 / 造村民 / 练兵 / 升级时代
 *--------------------------------------------------------------------------*/
void UsrAI::manageBuildingActions(const tagInfo& inf)
{
    // 科技指令结果核查（ins_ret 窗口短，必须每帧最前）
    for (int i = 0; i < R_NUM; ++i) {
        if (s_res[i].id < 0 || s_res[i].done) continue;
        map<int, int>::const_iterator it = inf.ins_ret.find(s_res[i].id);
        if (it != inf.ins_ret.end()) {
            if (it->second == ACTION_SUCCESS) s_res[i].done = true;
            else s_res[i].cdUntil = inf.GameFrame + 600;   // 失败退避重试
            s_res[i].id = -1;
        } else if (inf.GameFrame - s_res[i].frame > 900) {
            s_res[i].id = -1;
            s_res[i].cdUntil = inf.GameFrame + 600;
        }
    }

    // 升级时代指令结果核查
    if (s_ageUpgOrdered && s_ageUpgId >= 0) {
        map<int, int>::const_iterator it = inf.ins_ret.find(s_ageUpgId);
        if (it != inf.ins_ret.end()) {
            if (it->second != ACTION_SUCCESS) {
                s_ageUpgOrdered = false;
                s_ageUpgCdUntil = inf.GameFrame + 600;
            }
            s_ageUpgId = -1;
        } else if (inf.GameFrame - s_ageUpgFrame > 900) {
            s_ageUpgOrdered = false;
            s_ageUpgId = -1;
            s_ageUpgCdUntil = inf.GameFrame + 600;
        }
    }

    bool popOk  = (inf.Human_Num < inf.Human_MaxNum - 0.5);
    bool bronze = (inf.civilizationStage >= CIVILIZATION_BRONZEAGE);

    // 兵力目标：第二波前10人、第三波前16人、之后20人（近战:远程各半）
    int armyTotal = (inf.GameFrame < 13500) ? 10 :
                    (inf.GameFrame < 21000) ? 16 : 20;
    int archerTarget = armyTotal / 2;
    int meleeTarget  = armyTotal - archerTarget;

    // 练兵许可：第一波结束后才造兵；升铜器指令下达前保住800食物基金
    bool mayTrain = (inf.GameFrame > 7500) &&
                    (bronze || s_ageUpgOrdered || inf.Meat >= 880);

    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        const tagBuilding& b = inf.buildings[i];
        if (b.Percent < 100) continue;
        if (b.Project != ACT_NULL && b.Type != BUILDING_ARROWTOWER)
            continue;                        // 忙碌（箭塔Project是攻击目标）

        if (b.Type == BUILDING_GRANARY) {
            if (!s_res[R_TOWER_UNLOCK].done && s_res[R_TOWER_UNLOCK].id < 0 &&
                inf.GameFrame >= s_res[R_TOWER_UNLOCK].cdUntil &&
                inf.GameFrame > 150 && inf.Meat >= 50) {
                s_res[R_TOWER_UNLOCK].id =
                    BuildingAction(b.SN, BUILDING_GRANARY_ARROWTOWER);
                s_res[R_TOWER_UNLOCK].frame = inf.GameFrame;
            }
            else if (!s_res[R_TOWER_UPG].done && s_res[R_TOWER_UPG].id < 0 &&
                     inf.GameFrame >= s_res[R_TOWER_UPG].cdUntil &&
                     inf.GameFrame > 5000 && inf.Meat >= 120 && inf.Stone >= 50) {
                // 箭塔强化：攻+1 射程+1，第二波前完成
                s_res[R_TOWER_UPG].id =
                    BuildingAction(b.SN, BUILDING_GRANARY_ARROWTOWE_UPGRADE);
                s_res[R_TOWER_UPG].frame = inf.GameFrame;
            }
        }
        else if (b.Type == BUILDING_MARKET) {
            if (!s_res[R_WOOD].done && s_res[R_WOOD].id < 0 &&
                inf.GameFrame >= s_res[R_WOOD].cdUntil &&
                inf.GameFrame > 1500 && inf.Meat >= 120 && inf.Wood >= 75) {
                // 木材加工：采集率 0.02→0.22（11倍），最高性价比科技
                s_res[R_WOOD].id = BuildingAction(b.SN, BUILDING_MARKET_WOOD_UPGRADE);
                s_res[R_WOOD].frame = inf.GameFrame;
            }
            else if (!s_res[R_FARM].done && s_res[R_FARM].id < 0 &&
                     inf.GameFrame >= s_res[R_FARM].cdUntil &&
                     bronze && inf.Meat >= 200 && inf.Wood >= 50) {
                s_res[R_FARM].id = BuildingAction(b.SN, BUILDING_MARKET_FARM_UPGRADE);
                s_res[R_FARM].frame = inf.GameFrame;
            }
        }
        else if (b.Type == BUILDING_CENTER) {
            // 最高优先级：升级铜器（前置=市场+靶场建成，800食物，60秒）
            if (!bronze && !s_ageUpgOrdered &&
                inf.GameFrame >= s_ageUpgCdUntil &&
                countDoneBuilding(inf, BUILDING_MARKET) > 0 &&
                countDoneBuilding(inf, BUILDING_RANGE) > 0 &&
                inf.Meat >= 800) {
                s_ageUpgId = BuildingAction(b.SN, BUILDING_CENTER_UPGRADE);
                s_ageUpgFrame = inf.GameFrame;
                s_ageUpgOrdered = true;
            }
            else if (popOk) {
                // 村民持续生产（v3：不再限制开局窗口）
                int target = 8 + inf.GameFrame / 450;
                if (target > 36) target = 36;
                // 升铜器基金保护：8500帧后未升级则攒钱
                int reserve = (!bronze && !s_ageUpgOrdered &&
                               inf.GameFrame > 8500) ? 900 : 150;
                if ((int)inf.farmers.size() < target && inf.Meat >= reserve)
                    BuildingAction(b.SN, BUILDING_CENTER_CREATEFARMER);
            }
        }
        else if (b.Type == BUILDING_ARMYCAMP) {
            if (bronze && !s_res[R_CLUB].done && s_res[R_CLUB].id < 0 &&
                inf.GameFrame >= s_res[R_CLUB].cdUntil && inf.Meat >= 100) {
                s_res[R_CLUB].id =
                    BuildingAction(b.SN, BUILDING_ARMYCAMP_UPGRADE_CLUBMAN);
                s_res[R_CLUB].frame = inf.GameFrame;
            }
            else if (bronze && !s_res[R_BROAD].done && s_res[R_BROAD].id < 0 &&
                     inf.GameFrame >= s_res[R_BROAD].cdUntil &&
                     inf.Meat >= 140 && inf.Gold >= 50) {
                s_res[R_BROAD].id =
                    BuildingAction(b.SN, BUILDING_ARMYCAMP_UPGRADE_BROADSWORD);
                s_res[R_BROAD].frame = inf.GameFrame;
            }
            else if (mayTrain && popOk &&
                     inf.GameFrame - s_trainCdFrame >= 90 &&
                     countMelee(inf) < meleeTarget) {
                if (s_res[R_BROAD].done && inf.Meat >= 35 && inf.Gold >= 15)
                    BuildingAction(b.SN, BUILDING_ARMYCAMP_CREATE_BROADSWORD);
                else if (inf.Meat >= 50)
                    BuildingAction(b.SN, BUILDING_ARMYCAMP_CREATE_CLUBMAN);
                s_trainCdFrame = inf.GameFrame;
            }
        }
        else if (b.Type == BUILDING_RANGE) {
            if (mayTrain && popOk && inf.GameFrame - s_trainCdFrame >= 90 &&
                countArchers(inf) < archerTarget &&
                inf.Meat >= 40 && inf.Wood >= 20) {
                BuildingAction(b.SN, BUILDING_RANGE_CREATE_BOWMAN);
                s_trainCdFrame = inf.GameFrame;
            }
        }
    }
}

/*----------------------------------------------------------------------------
 * 3. 村民管理：逃跑 > 上交 > 配额分工采集
 *--------------------------------------------------------------------------*/
void UsrAI::manageFarmers(const tagInfo& inf)
{
    double fleeR = 5.0 * s_bls;

    for (size_t i = 0; i < inf.farmers.size(); ++i) {
        const tagFarmer& f = inf.farmers[i];
        if (f.FarmerSort != FARMERTYPE_FARMER) continue;

        // 核对上一条指令的执行结果（窗口短，放最前）
        {
            int lastId = -1;
            map<int, int>::iterator idIt = s_farmerCmdId.find(f.SN);
            if (idIt != s_farmerCmdId.end()) lastId = idIt->second;
            if (lastId >= 0) {
                map<int, int>::const_iterator r = inf.ins_ret.find(lastId);
                if (r != inf.ins_ret.end()) {
                    if (r->second != ACTION_SUCCESS) {
                        int lt = -1; char lk = 0;
                        map<int, int>::iterator tIt = s_farmerCmdTarget.find(f.SN);
                        if (tIt != s_farmerCmdTarget.end()) lt = tIt->second;
                        map<int, char>::iterator kIt = s_farmerCmdKind.find(f.SN);
                        if (kIt != s_farmerCmdKind.end()) lk = kIt->second;
                        if (lt > 0 && lk != 'M')
                            s_targetBadUntil[lt] = inf.GameFrame + 1200;
                        s_farmerStuck[f.SN] += 1;
                    }
                    s_farmerCmdId[f.SN] = -1;
                }
            }
        }

        // 1) 保命：敌军5格内向远离方向撤退
        const tagArmy* en = nearestEnemy(inf, f.DR, f.UR);
        if (en && dist2(f.DR, f.UR, en->DR, en->UR) < fleeR * fleeR) {
            int last = -1000;
            map<int, int>::iterator lf = s_lastFleeFrame.find(f.SN);
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

        // 2) 本帧刚被派去建造的村民跳过
        bool isBuilder = false;
        for (int k = 0; k < 2; ++k)
            if (s_pend[k].id >= 0 && s_pend[k].builderSN == f.SN) {
                isBuilder = true;
                break;
            }
        if (isBuilder) continue;
        if (f.NowState != HUMAN_STATE_IDLE) continue;

        // 3) 指令冷却（12帧）
        int lastFrame = -999;
        { map<int, int>::iterator it = s_farmerCmdFrame.find(f.SN);
          if (it != s_farmerCmdFrame.end()) lastFrame = it->second; }
        if (inf.GameFrame - lastFrame < 12) continue;

        int lastKind   = 0;
        int lastTarget = -1;
        { map<int, char>::iterator it = s_farmerCmdKind.find(f.SN);
          if (it != s_farmerCmdKind.end()) lastKind = it->second; }
        { map<int, int>::iterator it = s_farmerCmdTarget.find(f.SN);
          if (it != s_farmerCmdTarget.end()) lastTarget = it->second; }

        // 4) 快速回空闲 = 目标没采成
        bool quickReturn = (inf.GameFrame - lastFrame < 300);
        if (quickReturn) {
            if (lastKind == 'G' || lastKind == 'M') s_farmerStuck[f.SN] += 1;
        } else {
            s_farmerStuck[f.SN] = 0;
        }

        // 5) 卡住3次：先随机挪位再重新指派
        int stuck = 0;
        { map<int, int>::iterator it = s_farmerStuck.find(f.SN);
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

        // 6) 手持资源 -> 上交（浆果/猎物/木/石/金交仓库，农田食物交谷仓，
        //    市镇中心兜底）
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

        // 7) 手空 -> 动态配额分工 + 满员检查的就近采集
        char role = pickRole(inf);
        s_farmerRole[f.SN] = role;
        int exclude = (quickReturn && lastKind == 'G') ? lastTarget : -1;
        int sn = nearestResourceSN(inf, f.DR, f.UR, role, exclude, f.SN);
        if (sn < 0 && role != 'W') {          // 本职无目标（如8块田已满员）
            if (role == 'F') s_farmerRole[f.SN] = 'W';   // 食物满员转伐木
            sn = nearestResourceSN(inf, f.DR, f.UR, 'W', exclude, f.SN);
        }
        if (sn < 0 && role == 'W') {          // 木材也没有 -> 尝试食物
            sn = nearestResourceSN(inf, f.DR, f.UR, 'F', exclude, f.SN);
            if (sn >= 0) s_farmerRole[f.SN] = 'F';
        }
        if (sn >= 0) {
            int id = HumanAction(f.SN, sn);
            noteFarmerCmd(f.SN, id, sn, 'G', inf.GameFrame);
        } else {
            // 周围无任何可采资源：向市镇中心靠拢待命
            const tagBuilding* tc = nearestBuilding(inf, BUILDING_CENTER,
                                                    f.DR, f.UR, true);
            if (tc) {
                double tx = blockCenter(tc->BlockDR), ty = blockCenter(tc->BlockUR);
                double d = 4.0 * s_bls;
                if (dist2(f.DR, f.UR, tx, ty) > d * d) {
                    HumanMove(f.SN, tx, ty);
                    noteFarmerCmd(f.SN, -1, -1, 'M', inf.GameFrame);
                }
            }
        }
    }
}

/*----------------------------------------------------------------------------
 * 4. 祭司管理（v3 全重写）
 *    优先级：敌军贴脸逃塔 > 庇护窗口回塔 > 探路窗口 > 常驻塔下
 *    庇护窗口：波次出生前1500帧 ~ 抵达后清理完毕
 *      第一波6000 → [4500, 7800]；第二波13500 → [11800, 16000]；
 *      第三波21000 → [19800, ∞)
 *    探路窗口：波次间隙。修复v2刷屏根因：
 *      a) 移动指令统一90帧冷却（v2在IDLE时每帧重发）
 *      b) ins_ret 失败 → 立即拉黑该路点
 *      c) 下令600帧后位移<0.8格 → 拉黑该路点
 *--------------------------------------------------------------------------*/
static bool inShelterWindow(int fr)
{
    return (fr >= 4500  && fr <= 7800)  ||
           (fr >= 11800 && fr <= 16000) ||
           (fr >= 19800);
}

void UsrAI::managePriest(const tagInfo& inf)
{
    const tagArmy* p = findPriest(inf);
    if (!p) return;

    // 0) 核对上一条祭司指令：失败（多为不可达）→ 拉黑对应路点
    if (s_priestCmdId >= 0) {
        map<int, int>::const_iterator r = inf.ins_ret.find(s_priestCmdId);
        if (r != inf.ins_ret.end()) {
            if (r->second != ACTION_SUCCESS && s_priestCmdWp >= 0 &&
                s_priestCmdWp < SCOUT_NUM)
                s_wpBad[s_priestCmdWp] = true;
            s_priestCmdId = -1;
            s_priestCmdWp = -1;
        }
    }

    const tagArmy* en = nearestEnemy(inf, p->DR, p->UR);
    double dEn = en ? sqrt(dist2(p->DR, p->UR, en->DR, en->UR)) : 1e18;

    // 1) 敌军12格内：撤向最近未被压制的箭塔（高频冷却15帧）
    if (en && dEn < 12.0 * s_bls) {
        const tagBuilding* tw = NULL;
        double bd = 1e18;
        for (size_t i = 0; i < inf.buildings.size(); ++i) {
            const tagBuilding& b = inf.buildings[i];
            if (b.Type != BUILDING_ARROWTOWER || b.Percent < 100) continue;
            double tx = blockCenter(b.BlockDR), ty = blockCenter(b.BlockUR);
            double dPt = sqrt(dist2(p->DR, p->UR, tx, ty));
            double dEt = sqrt(dist2(en->DR, en->UR, tx, ty));
            if (dEt < 6.0 * s_bls && dPt > dEt) continue;  // 该塔被压制
            if (dPt < bd) { bd = dPt; tw = &b; }
        }
        if (tw) {
            double tx = blockCenter(tw->BlockDR), ty = blockCenter(tw->BlockUR);
            if (sqrt(dist2(p->DR, p->UR, tx, ty)) > 2.5 * s_bls &&
                inf.GameFrame - s_priestCmdFrame >= 15) {
                int id = HumanMove(p->SN, tx, ty);
                s_priestCmdFrame = inf.GameFrame;
                s_priestCmdId = id;
                s_priestCmdWp = -1;
            }
        } else if (inf.GameFrame - s_priestCmdFrame >= 15) {
            double ddr = p->DR - en->DR, dur = p->UR - en->UR;
            double len = sqrt(ddr * ddr + dur * dur);
            if (len < 1e-6) { ddr = 1.0; dur = 0.0; len = 1.0; }
            double tx = p->DR + ddr / len * 14.0 * s_bls;
            double ty = p->UR + dur / len * 14.0 * s_bls;
            clampDetail(tx, ty);
            int id = HumanMove(p->SN, tx, ty);
            s_priestCmdFrame = inf.GameFrame;
            s_priestCmdId = id;
            s_priestCmdWp = -1;
        }
        return;
    }

    // 2) 庇护窗口 / 敌军25格内：回最近箭塔下驻守（冷却60帧）
    bool shelter = inShelterWindow(inf.GameFrame) || (en && dEn < 25.0 * s_bls);
    if (shelter) {
        const tagBuilding* tw = nearestBuilding(inf, BUILDING_ARROWTOWER,
                                                p->DR, p->UR, true);
        if (!tw)
            tw = nearestBuilding(inf, BUILDING_CENTER, p->DR, p->UR, true);
        if (tw) {
            double tx = blockCenter(tw->BlockDR), ty = blockCenter(tw->BlockUR);
            if (sqrt(dist2(p->DR, p->UR, tx, ty)) > 2.5 * s_bls &&
                inf.GameFrame - s_priestCmdFrame >= 60) {
                int id = HumanMove(p->SN, tx, ty);
                s_priestCmdFrame = inf.GameFrame;
                s_priestCmdId = id;
                s_priestCmdWp = -1;
            }
        }
        return;
    }

    // 3) 探路窗口：波次间隙外出侦察（同时避开狮子）
    if (inf.GameFrame > 300 && s_scoutIdx < SCOUT_NUM) {
        // 狮子规避：2.5格内有狮子则绕开（冷却45帧）
        if (inf.GameFrame - s_priestCmdFrame >= 45) {
            for (size_t i = 0; i < inf.resources.size(); ++i) {
                const tagResource& r = inf.resources[i];
                if (r.Type != RESOURCE_LION || r.Cnt <= 0) continue;
                double lim = 2.5 * s_bls;
                if (dist2(p->DR, p->UR, r.DR, r.UR) < lim * lim) {
                    double ddr = p->DR - r.DR, dur = p->UR - r.UR;
                    double len = sqrt(ddr * ddr + dur * dur);
                    if (len < 1e-6) { ddr = 1.0; dur = 0.0; len = 1.0; }
                    double tx = p->DR + ddr / len * 6.0 * s_bls;
                    double ty = p->UR + dur / len * 6.0 * s_bls;
                    clampDetail(tx, ty);
                    int id = HumanMove(p->SN, tx, ty);
                    s_priestCmdFrame = inf.GameFrame;
                    s_priestCmdId = id;
                    s_priestCmdWp = -1;
                    return;
                }
            }
        }

        // 跳过已到达/被拉黑的路点
        while (s_scoutIdx < SCOUT_NUM &&
               (s_wpVisited[s_scoutIdx] || s_wpBad[s_scoutIdx]))
            ++s_scoutIdx;
        if (s_scoutIdx < SCOUT_NUM) {
            double tx = blockCenter(SCOUT_WAYPOINTS[s_scoutIdx][0]);
            double ty = blockCenter(SCOUT_WAYPOINTS[s_scoutIdx][1]);
            double reach = 4.0 * s_bls;
            if (dist2(p->DR, p->UR, tx, ty) <= reach * reach) {
                s_wpVisited[s_scoutIdx] = true;   // 已到达，转下一路点
                ++s_scoutIdx;
            } else {
                // 无位移检测：每600帧快照一次，同一路点期间位移<0.8格
                // → 该路点不可达（隔水/被地形卡死），永久拉黑
                if (inf.GameFrame - s_priestSnapFrame >= 600) {
                    if (s_priestSnapWp == s_scoutIdx && s_priestSnapFrame > 0) {
                        double lim = 0.8 * s_bls;
                        if (dist2(p->DR, p->UR,
                                  s_priestSnapDR, s_priestSnapUR) < lim * lim) {
                            s_wpBad[s_scoutIdx] = true;
                            ++s_scoutIdx;
                            return;
                        }
                    }
                    s_priestSnapDR = p->DR;
                    s_priestSnapUR = p->UR;
                    s_priestSnapFrame = inf.GameFrame;
                    s_priestSnapWp = s_scoutIdx;
                }
                // 统一90帧冷却 + 仅在IDLE时下令（避免重置行进路径）
                if (p->NowState == HUMAN_STATE_IDLE &&
                    inf.GameFrame - s_priestCmdFrame >= 90) {
                    int id = HumanMove(p->SN, tx, ty);
                    s_priestCmdFrame = inf.GameFrame;
                    s_priestCmdId = id;
                    s_priestCmdWp = s_scoutIdx;
                }
            }
            return;
        }
    }

    // 4) 默认驻守：最近的已建成箭塔旁（冷却60帧）
    const tagBuilding* tw = nearestBuilding(inf, BUILDING_ARROWTOWER,
                                            p->DR, p->UR, true);
    if (!tw)
        tw = nearestBuilding(inf, BUILDING_CENTER, p->DR, p->UR, true);
    if (tw && p->NowState == HUMAN_STATE_IDLE) {
        double tx = blockCenter(tw->BlockDR), ty = blockCenter(tw->BlockUR);
        double d = 3.0 * s_bls;
        if (dist2(p->DR, p->UR, tx, ty) > d * d &&
            inf.GameFrame - s_priestCmdFrame >= 60) {
            int id = HumanMove(p->SN, tx, ty);
            s_priestCmdFrame = inf.GameFrame;
            s_priestCmdId = id;
            s_priestCmdWp = -1;
        }
    }
}

/*----------------------------------------------------------------------------
 * 5. 箭塔管理：空闲箭塔对射程内敌军自动开火（重复下令会重置攻击）
 *--------------------------------------------------------------------------*/
void UsrAI::manageTowers(const tagInfo& inf)
{
    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        const tagBuilding& b = inf.buildings[i];
        if (b.Type != BUILDING_ARROWTOWER || b.Percent < 100) continue;
        if (b.Project >= 0) continue;   // 已有攻击目标

        int last = -1000;
        map<int, int>::iterator it = s_towerCmdFrame.find(b.SN);
        if (it != s_towerCmdFrame.end()) last = it->second;
        if (inf.GameFrame - last < 10) continue;

        double tx = blockCenter(b.BlockDR), ty = blockCenter(b.BlockUR);
        const tagArmy* en = nearestEnemy(inf, tx, ty);
        if (!en) continue;
        double range = 8.0 * s_bls;     // 射程7格（强化后8格），留余量
        if (dist2(tx, ty, en->DR, en->UR) < range * range) {
            HumanAction(b.SN, en->SN);
            s_towerCmdFrame[b.SN] = inf.GameFrame;
        }
    }
}

/*----------------------------------------------------------------------------
 * 6. 军队管理：护祭司优先；敌军在基地警戒圈(28格)内才出击，
 *    避免全军追击到地图远处；无敌情时集结在塔簇（TC东南）
 *--------------------------------------------------------------------------*/
void UsrAI::manageArmies(const tagInfo& inf)
{
    if (s_tcDR < 0) return;
    double gx = blockCenter(s_tcDR + 4), gy = blockCenter(s_tcUR + 4);
    double d = 3.0 * s_bls;
    double tcx = blockCenter(s_tcDR), tcy = blockCenter(s_tcUR);
    double engageR = 28.0 * s_bls;

    // 护祭司：锁定进入祭司20格内的敌军
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
            map<int, int>::iterator it = s_armyCmdFrame.find(a.SN);
            if (it != s_armyCmdFrame.end()) last = it->second;
            if (inf.GameFrame - last < 15) continue;

            const tagArmy* target = threat;
            if (!target) {
                // 只攻击基地警戒圈内的敌军
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
            map<int, int>::iterator it = s_armyCmdFrame.find(a.SN);
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

    // 首帧初始化
    if (s_tcDR < 0) {
        s_bls = BLOCKSIDELENGTH;
        for (int i = 0; i < R_NUM; ++i) {
            s_res[i].id = -1;
            s_res[i].frame = 0;
            s_res[i].cdUntil = 0;
            s_res[i].done = false;
        }
        s_ageUpgId = -1;
        s_ageUpgOrdered = false;
        s_priestCmdId = -1;
        s_priestCmdWp = -1;
        s_priestCmdFrame = -999;
        s_trainCdFrame = 0;
        for (int k = 0; k < 2; ++k) {
            s_pend[k].id = -1;
            s_pend[k].type = -1;
            s_pend[k].posIdx = -1;
            s_pend[k].frame = 0;
            s_pend[k].builderSN = -1;
        }
        const tagBuilding* tc = NULL;
        for (size_t i = 0; i < inf.buildings.size(); ++i) {
            if (inf.buildings[i].Type == BUILDING_CENTER) {
                tc = &inf.buildings[i];
                break;
            }
        }
        if (tc) { s_tcDR = tc->BlockDR; s_tcUR = tc->BlockUR; }
        else    { s_tcDR = 22; s_tcUR = 20; }
    }

    // 累计新探索块（供探路参考）
    updateExplored(inf);

    // 周期性清理阵亡村民的状态
    if (inf.GameFrame % 600 == 0) cleanFarmerMaps(inf);

    manageBuild(inf);           // 建造（双槽位并行）
    manageBuildingActions(inf); // 研发/造村民/练兵/升级
    manageFarmers(inf);         // 村民
    managePriest(inf);          // 祭司
    manageTowers(inf);          // 箭塔
    manageArmies(inf);          // 军队

    // 周期性状态输出（每600帧=24秒）
    if (inf.GameFrame % 600 == 0) {
        const tagArmy* priest = findPriest(inf);
        DebugText(QString(
            "[AIv3] f=%1 meat=%2 wood=%3 stone=%4 gold=%5 pop=%6/%7 civ=%8 "
            "farm=%9 army=%10 scout=%11/%12 priestHp=%13 tw=%14")
            .arg(inf.GameFrame).arg(inf.Meat).arg(inf.Wood).arg(inf.Stone)
            .arg(inf.Gold)
            .arg(inf.Human_Num).arg(inf.Human_MaxNum)
            .arg(inf.civilizationStage)
            .arg((int)inf.farmers.size())
            .arg(armyCountNonPriest(inf))
            .arg(s_scoutIdx).arg(SCOUT_NUM)
            .arg(priest ? priest->Blood : 0)
            .arg(countAnyBuilding(inf, BUILDING_ARROWTOWER)));
    }
}
