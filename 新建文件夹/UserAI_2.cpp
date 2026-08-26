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
 * 初版 AI v2 —— 目标：及格线（存活10分钟 + 升级到铜器时代）
 *
 * 策略概要：
 *   1. 经济：村民按 3:2 分工采集食物/木材；开局前1.6分钟持续造村民到12人；
 *            可见食物枯竭时用市场补农田
 *   2. 建筑：兵营(125木) -> 市场(150木) -> 靶场(150木)（满足升铜器的
 *            “2个工具时代建筑”前置）-> 房屋(30木,按人口) -> 2座箭塔(各150石)
 *   3. 科技：谷仓一次性研发“箭塔解锁”(50食)；市镇中心在市场+靶场建成后
 *            囤够800食物立即升级铜器时代(60秒)
 *   4. 军事：兵营持续训练棍棒兵，第一波(6000帧)前6个、第二波(13500帧)
 *            前12个、之后16个；敌军接近祭司时全军优先拦截
 *   5. 祭司：无敌情时探图(11000帧前，沿固定路点)；遇袭撤向最近箭塔
 *            寻求庇护（箭塔射程7格）；探图结束驻守箭塔旁
 *
 * v2 修订（针对首轮测试的 5 个问题）：
 *   [问题1/3] 祭司不再原地待命——增加探图状态机（见 managePriest）
 *   [问题2]   祭司遇袭逃向箭塔而非远离方向；军队优先攻击接近祭司的敌军；
 *             箭塔由 AI 下令开火（Project>=0 表示已有目标，-1 为空闲）
 *   [问题4/5] 村民指令增加防抖机制：
 *             - 同一村民 12 帧内不重复下令（消除 debug 刷屏）
 *             - 每条指令通过 ins_ret 核对结果，失败则拉黑该目标 1200 帧
 *             - 下令后 300 帧内又变空闲 = 目标没采成(不可达/被中断)，
 *               下次自动换一个目标（目标轮换）
 *             - 连续 3 次快速回空闲 = 可能被卡住，先随机挪位再重新指派
 *             - 上交资源时市镇中心兜底（内核规则：市镇中心接受所有资源类型，
 *               谷仓只收农田食物GRANARYFOOD，仓库收木/石/金/浆果/猎物；
 *               类型不匹配时内核会转成“修理”，建筑满血即失败——这就是
 *               首轮“设定谷仓/仓库后无动作且重复执行”的根源）
 *
 * 敌方进攻节奏（地图预置，不会补充）：
 *   第一波 ~6000帧(4分钟)：2斧头兵+1弓箭手
 *   第二波 ~13500帧(9分钟)：+方阵兵/阔剑兵/复合弓兵/战车弓兵（战车弓兵优先猎杀祭司）
 *   第三波 ~21000帧(14分钟)：约10个铜器单位+2投石车（及格线只需活到10分钟）
 *
 * 引擎机制备忘（源码核实）：
 *   - 采集指令下达后内核自动“采集->上交->返回”循环，无需每帧重发
 *   - 上交(对己方建筑 HumanAction)无距离要求，瞬间完成
 *   - 指令按单位去重(同一单位每帧只保留最后一条)；每帧最多处理
 *     “建筑数+人口数”条指令，多余指令直接丢弃
 *   - 250帧无进展或无路可走的行动会被内核强制中断，单位回到空闲
 *   - 箭塔 Project 字段：-1 空闲 / >=0 当前攻击目标 SN
 *==========================================================================*/
#include <map>
#include <vector>
#include <cmath>

tagInfo info;

/*----------------------------------------------------------------------------
 * 全局策略状态
 *--------------------------------------------------------------------------*/
static double s_bls = 35.777;             // 块边长 BLOCKSIDELENGTH（首帧从配置读取）
static int    s_tcDR = -1, s_tcUR = -1;   // 市镇中心块坐标（建造/集结的参照点）

static bool s_towerResearched   = false;  // 谷仓“研发箭塔”是否已成功
static int  s_towerResearchId   = -1;     // 箭塔研发指令 id（用于查结果）
static int  s_towerResearchFrame = 0;

static int s_buildIdx        = 0;   // 建造候选位置游标
static int s_pendingBuildId  = -1;  // 在途建造指令 id
static int s_pendingPosIdx   = -1;  // 在途建造使用的候选位置下标
static int s_pendingFrame    = 0;   // 在途指令发出帧（超时保护）
static int s_builderSN       = -1;  // 本帧刚被派去建造的村民（跳过其采集指派）

static map<int, char> s_farmerRole;    // 村民SN -> 'F'食物 / 'W'木材
static map<int, int>  s_lastFleeFrame; // 单位SN -> 上次逃跑帧（控制指令频率）

/*--- v2：村民指令防抖与防卡死 ---*/
static map<int, int>  s_farmerCmdFrame;  // 村民SN -> 上次下令帧
static map<int, int>  s_farmerCmdId;     // 村民SN -> 上次下令的指令id（查ins_ret）
static map<int, int>  s_farmerCmdTarget; // 村民SN -> 上次下令目标SN
static map<int, char> s_farmerCmdKind;   // 'G'采集 / 'D'上交 / 'M'移动
static map<int, int>  s_farmerStuck;     // 村民SN -> 连续“快速回空闲”次数
static map<int, int>  s_targetBadUntil;  // 目标SN -> 拉黑截止帧（指令失败）

/*--- v2：祭司探图 ---*/
static set<int> s_exploredKey;          // 已探索块集合（key = DR*1000+UR）
static int s_scoutIdx          = 0;     // 当前探图路点下标
static int s_scoutWpFrame      = 0;     // 当前路点启程帧（超时跳过）
static int s_priestCmdFrame    = -999;  // 祭司上次下令帧

/* 祭司探图路点（绝对块坐标；由近及远、由安全方向到危险方向排列；
 * 敌方基地在东南(86,86)，故先探北/西，最后才向中央推进） */
static const int SCOUT_WAYPOINTS[][2] = {
    {22,  6}, { 6, 20}, {36, 12}, {10, 36},   // 基地近环：北/西/东北/西南
    {44, 24}, {24, 44}, {48, 44}, {44, 48},   // 中环：向东/南及地图中央
    {60, 30}, {30, 60}, {56, 56}              // 远环（为后续进攻探路）
};
static const int SCOUT_NUM =
    (int)(sizeof(SCOUT_WAYPOINTS) / sizeof(SCOUT_WAYPOINTS[0]));

/*--- v2：军队/箭塔指令冷却 ---*/
static map<int, int> s_armyCmdFrame;   // 军队SN -> 上次下令帧
static map<int, int> s_towerCmdFrame;  // 箭塔SN -> 上次下令帧

/* 建造候选位置（相对市镇中心的块坐标偏移，顺序即使用顺序）
 * 前3个给兵营/市场/靶场，中间给房屋，{4,10}/{10,4}留给箭塔（东南方向，敌方来向） */
static const int BUILD_OFFSETS[][2] = {
    { 5,  5}, { 2,  9}, { 9,  2},                     // 兵营/市场/靶场
    { 6, 12}, {12,  6}, { 9,  9}, {-5,  5}, { 5, -5}, // 房屋
    { 4, 10}, {10,  4},                               // 箭塔（东南）
    {-2,  9}, { 9, -2}, {12, 12}, {-9,  5}, { 5, -9},
    {-9, -5}, {-5, -9}, {-9, -9},
    {13,  7}, { 7, 13}, {-13,  5}, {13, -5}, { 5,-13}, {-5, 13},
    {-5,-13}, {-13, -5}, {14, 14}, {-14,  7}, { 7,-14}, {14, -7},
    {-7, 14}, {-7,-14}, {-14,-14}
};
static const int BUILD_OFFSETS_NUM =
    (int)(sizeof(BUILD_OFFSETS) / sizeof(BUILD_OFFSETS[0]));

/*----------------------------------------------------------------------------
 * 通用小工具
 *--------------------------------------------------------------------------*/
static double dist2(double dr1, double ur1, double dr2, double ur2)
{
    double a = dr1 - dr2, b = ur1 - ur2;
    return a * a + b * b;
}

static double blockCenter(int b) { return (b + 0.5) * s_bls; }

/* 把细节坐标钳制在地图范围内的合法块中心 */
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

/* 找离(dr,ur)最近的某类己方建筑（doneOnly=true 时只算已建成的） */
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

/* 该目标是否处于拉黑期（指令失败后 1200 帧内不再作为目标） */
static bool targetBad(const tagInfo& inf, int sn)
{
    map<int, int>::const_iterator it = s_targetBadUntil.find(sn);
    return it != s_targetBadUntil.end() && inf.GameFrame < it->second;
}

/* 累计本帧新探索的块（exploredUpdate 为“本轮新增探索块”坐标） */
static void updateExplored(const tagInfo& inf)
{
    for (size_t i = 0; i < inf.exploredUpdate.size(); ++i)
        s_exploredKey.insert(inf.exploredUpdate[i].x * 1000 +
                             inf.exploredUpdate[i].y);
}

static bool blockExplored(int dr, int ur)
{
    return s_exploredKey.count(dr * 1000 + ur) > 0;
}

/* 村民分工：保持 食物:木材 ≈ 3:2 */
static char farmerRole(int sn)
{
    map<int, char>::iterator it = s_farmerRole.find(sn);
    if (it != s_farmerRole.end()) return it->second;
    int f = 0, w = 0;
    for (map<int, char>::iterator i = s_farmerRole.begin();
         i != s_farmerRole.end(); ++i) {
        if (i->second == 'F') ++f; else ++w;
    }
    char r = (f * 2 <= w * 3) ? 'F' : 'W';
    s_farmerRole[sn] = r;
    return r;
}

/* 按分工找最近可采资源：食物=浆果/羚羊/象（不招惹狮子），木材=树；
 * excludeSN = 需要跳过的目标（快速回空闲时换目标用） */
static int nearestResourceSN(const tagInfo& inf, double dr, double ur,
                             char role, int excludeSN)
{
    int sn = -1;
    double bd = 1e18;
    for (size_t i = 0; i < inf.resources.size(); ++i) {
        const tagResource& r = inf.resources[i];
        if (r.Cnt <= 0) continue;
        if (r.SN == excludeSN) continue;       // 目标轮换：跳过上次可疑目标
        if (targetBad(inf, r.SN)) continue;    // 指令失败被拉黑的目标
        bool ok;
        if (role == 'F')
            ok = (r.Type == RESOURCE_BUSH || r.Type == RESOURCE_GAZELLE ||
                  r.Type == RESOURCE_ELEPHANT);
        else
            ok = (r.Type == RESOURCE_TREE);
        if (!ok) continue;
        double d = dist2(dr, ur, r.DR, r.UR);
        if (d < bd) { bd = d; sn = r.SN; }
    }
    if (sn < 0 && role == 'F') { // 农田兜底
        for (size_t i = 0; i < inf.buildings.size(); ++i) {
            const tagBuilding& b = inf.buildings[i];
            if (b.Type != BUILDING_FARM || b.Percent < 100 || b.Cnt <= 0) continue;
            if (b.SN == excludeSN || targetBad(inf, b.SN)) continue;
            double d = dist2(dr, ur, blockCenter(b.BlockDR), blockCenter(b.BlockUR));
            if (d < bd) { bd = d; sn = b.SN; }
        }
    }
    return sn;
}

/* 可见食物总量（浆果+猎物+农田剩余），用于判断是否需要补农田 */
static int visibleFoodTotal(const tagInfo& inf)
{
    int n = 0;
    for (size_t i = 0; i < inf.resources.size(); ++i) {
        const tagResource& r = inf.resources[i];
        if (r.Type == RESOURCE_BUSH || r.Type == RESOURCE_GAZELLE ||
            r.Type == RESOURCE_ELEPHANT || r.Type == RESOURCE_LION)
            n += r.Cnt;
    }
    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        const tagBuilding& b = inf.buildings[i];
        if (b.Type == BUILDING_FARM && b.Percent >= 100) n += b.Cnt;
    }
    return n;
}

/* 记录一条村民指令（统一入口，方便维护） */
static void noteFarmerCmd(int sn, int id, int target, char kind, int frame)
{
    s_farmerCmdId[sn]     = id;
    s_farmerCmdTarget[sn] = target;
    s_farmerCmdKind[sn]   = kind;
    s_farmerCmdFrame[sn]  = frame;
}

/*----------------------------------------------------------------------------
 * 1. 建造管理：一次只安排一个建造，位置失败自动顺延到下一个候选点
 *--------------------------------------------------------------------------*/
void UsrAI::manageBuild(const tagInfo& inf)
{
    // 检查在途建造指令的结果
    if (s_pendingBuildId >= 0) {
        map<int, int>::const_iterator it = inf.ins_ret.find(s_pendingBuildId);
        if (it != inf.ins_ret.end()) {
            // 成功或失败都推进游标（失败说明该位置不合适，换个位置）
            s_buildIdx = s_pendingPosIdx + 1;
            s_pendingBuildId = -1;
        } else if (inf.GameFrame - s_pendingFrame > 900) {
            // 超时保护：推进游标，避免卡死在同一位置
            s_buildIdx = s_pendingPosIdx + 1;
            s_pendingBuildId = -1;
        }
    }
    if (s_pendingBuildId >= 0) return;           // 有建造在途，不再安排
    if (s_buildIdx >= BUILD_OFFSETS_NUM) return; // 候选位置用尽
    if (s_tcDR < 0) return;

    // 按优先级决定下一个要造的建筑
    int want = -1;
    if (countAnyBuilding(inf, BUILDING_ARMYCAMP) == 0 && inf.Wood >= 125)
        want = BUILDING_ARMYCAMP;                                  // 兵营
    else if (countAnyBuilding(inf, BUILDING_MARKET) == 0 &&
             countAnyBuilding(inf, BUILDING_ARMYCAMP) > 0 && inf.Wood >= 150)
        want = BUILDING_MARKET;                                    // 市场（升铜器前置1）
    else if (countAnyBuilding(inf, BUILDING_RANGE) == 0 &&
             countAnyBuilding(inf, BUILDING_MARKET) > 0 && inf.Wood >= 150)
        want = BUILDING_RANGE;                                     // 靶场（升铜器前置2）
    else if (inf.Human_Num >= inf.Human_MaxNum - 1 && inf.Wood >= 30)
        want = BUILDING_HOME;                                      // 房屋（人口将满）
    else if (countAnyBuilding(inf, BUILDING_ARROWTOWER) < 2 &&
             s_towerResearched && inf.Stone >= 150)
        want = BUILDING_ARROWTOWER;                                // 箭塔（用初始300石）
    else if (countAnyBuilding(inf, BUILDING_FARM) < 6 &&
             countAnyBuilding(inf, BUILDING_MARKET) > 0 && inf.Wood >= 75 &&
             visibleFoodTotal(inf) < 200)
        want = BUILDING_FARM;                                      // 食物枯竭补农田
    if (want < 0) return;

    // 计算建造块坐标
    int dr = s_tcDR + BUILD_OFFSETS[s_buildIdx][0];
    int ur = s_tcUR + BUILD_OFFSETS[s_buildIdx][1];
    if (dr < 1) dr = 1;
    if (dr > MAP_L - 3) dr = MAP_L - 3;
    if (ur < 1) ur = 1;
    if (ur > MAP_U - 3) ur = MAP_U - 3;

    // 找离建造点最近的空闲村民（优先用一段时间没接到指令的，避免打断采集）
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

    s_pendingBuildId = HumanBuild(builder->SN, want, dr, ur);
    s_pendingPosIdx  = s_buildIdx;
    s_pendingFrame   = inf.GameFrame;
    s_builderSN      = builder->SN;
    noteFarmerCmd(builder->SN, s_pendingBuildId, -1, 'M', inf.GameFrame);
}

/*----------------------------------------------------------------------------
 * 2. 建筑行动：研发箭塔 / 造村民 / 练兵 / 升级铜器时代
 *    说明：下达指令后建筑 Project 会变为非 ACT_NULL，天然防止重复下令
 *--------------------------------------------------------------------------*/
void UsrAI::manageBuildingActions(const tagInfo& inf)
{
    // 检查箭塔研发指令的结果
    if (s_towerResearchId >= 0) {
        map<int, int>::const_iterator it = inf.ins_ret.find(s_towerResearchId);
        if (it != inf.ins_ret.end()) {
            if (it->second == ACTION_SUCCESS) s_towerResearched = true;
            s_towerResearchId = -1;          // 失败则下轮重试
        } else if (inf.GameFrame - s_towerResearchFrame > 600) {
            s_towerResearchId = -1;
        }
    }

    bool popOk = (inf.Human_Num < inf.Human_MaxNum - 0.5);

    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        const tagBuilding& b = inf.buildings[i];
        if (b.Percent < 100) continue;       // 未建成
        if (b.Project != ACT_NULL && b.Type != BUILDING_ARROWTOWER)
            continue;                        // 忙碌中（箭塔的Project是攻击目标，另行处理）

        if (b.Type == BUILDING_GRANARY) {
            // 一次性研发：解锁箭塔（50食物/10秒）
            if (!s_towerResearched && s_towerResearchId < 0 &&
                inf.GameFrame > 200 && inf.Meat >= 50) {
                s_towerResearchId = BuildingAction(b.SN, BUILDING_GRANARY_ARROWTOWER);
                s_towerResearchFrame = inf.GameFrame;
            }
        }
        else if (b.Type == BUILDING_CENTER) {
            // 最高优先级：升级铜器时代（前置=市场+靶场建成，800食物，60秒）
            if (inf.civilizationStage == CIVILIZATION_TOOLAGE &&
                countDoneBuilding(inf, BUILDING_MARKET) > 0 &&
                countDoneBuilding(inf, BUILDING_RANGE) > 0 &&
                inf.Meat >= 800) {
                BuildingAction(b.SN, BUILDING_CENTER_UPGRADE);
            }
            // 前期持续造村民（50食物/20秒），目标12人
            else if (inf.GameFrame < 2400 &&
                     (int)inf.farmers.size() < 12 &&
                     inf.Meat >= 50 && popOk) {
                BuildingAction(b.SN, BUILDING_CENTER_CREATEFARMER);
            }
        }
        else if (b.Type == BUILDING_ARMYCAMP) {
            // 持续训练棍棒兵（50食物/27秒），按敌方进攻节奏定兵力目标
            int target = (inf.GameFrame < 6000)  ? 6  :
                         (inf.GameFrame < 13500) ? 12 : 16;
            if (armyCountNonPriest(inf) < target && inf.Meat >= 50 && popOk) {
                BuildingAction(b.SN, BUILDING_ARMYCAMP_CREATE_CLUBMAN);
            }
        }
    }
}

/*----------------------------------------------------------------------------
 * 3. 村民管理：逃跑 > 上交 > 采集
 *    v2：全部指令走“冷却 + 结果核对 + 目标轮换 + 卡住挪位”防抖机制
 *--------------------------------------------------------------------------*/
void UsrAI::manageFarmers(const tagInfo& inf)
{
    double fleeR = 5.0 * s_bls;

    for (size_t i = 0; i < inf.farmers.size(); ++i) {
        const tagFarmer& f = inf.farmers[i];
        if (f.FarmerSort != FARMERTYPE_FARMER) continue;

        // 核对上一条指令的执行结果：失败则拉黑目标并计入卡住计数
        // （注意：ins_ret 结果只在指令发出后的短窗口内可见，必须放在
        //   冷却/状态判断之前每帧核查，否则会错过结果）
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

        // 1) 保命：敌军5格内则向远离方向撤退（每25帧更新一次）
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

        if (f.SN == s_builderSN) continue;
        if (f.NowState != HUMAN_STATE_IDLE) continue;

        // 指令冷却：同一村民 12 帧内不重复下令
        // （消除信息快照滞后导致的重复指令与 debug 刷屏）
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

        // 快速回空闲：下令后 300 帧内又空闲，说明目标没采成（不可达/被
        // 内核强制中断）。采集与挪动指令计入卡住次数，上交不算（上交是
        // 瞬时完成的正常短指令）
        bool quickReturn = (inf.GameFrame - lastFrame < 300);
        if (quickReturn) {
            if (lastKind == 'G' || lastKind == 'M') s_farmerStuck[f.SN] += 1;
        } else {
            s_farmerStuck[f.SN] = 0;  // 长时间工作后归来，视为正常
        }

        // 卡住3次：先随机挪个位置（防止被卡在建筑/单位之间），再重新指派
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

        // 2) 手持资源 -> 上交（内核规则：浆果/猎物/木/石/金交仓库，
        //    农田食物交谷仓，市镇中心接受所有类型可兜底；
        //    类型不匹配会被内核转成“修理”，建筑满血时直接失败）
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

        // 3) 手空 -> 按分工就近采集（快速回空闲时排除上次的目标，强制轮换）
        char role = farmerRole(f.SN);
        int exclude = (quickReturn && lastKind == 'G') ? lastTarget : -1;
        int sn = nearestResourceSN(inf, f.DR, f.UR, role, exclude);
        if (sn < 0 && role == 'F') sn = nearestResourceSN(inf, f.DR, f.UR, 'W', exclude);
        if (sn >= 0) {
            int id = HumanAction(f.SN, sn);
            noteFarmerCmd(f.SN, id, sn, 'G', inf.GameFrame);
        } else {
            // 周围无资源可采：向市镇中心靠拢待命（避免原地发呆）
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
 * 4. 祭司管理：祭司死亡=直接失败，保命高于一切
 *    v2：遇袭撤向箭塔（而非乱跑）；无敌情时探图；平时驻守箭塔旁
 *--------------------------------------------------------------------------*/
void UsrAI::managePriest(const tagInfo& inf)
{
    const tagArmy* p = findPriest(inf);
    if (!p) return; // 祭司不在（已死亡或不可见），无能为力

    const tagArmy* en = nearestEnemy(inf, p->DR, p->UR);
    double dEn = en ? sqrt(dist2(p->DR, p->UR, en->DR, en->UR)) : 1e18;

    // 1) 敌军逼近（12格内，大于敌方视野）：撤向最近的箭塔寻求庇护
    if (en && dEn < 12.0 * s_bls) {
        // 选一座离祭司近、且没有被敌军贴脸的箭塔
        const tagBuilding* tw = NULL;
        double bd = 1e18;
        for (size_t i = 0; i < inf.buildings.size(); ++i) {
            const tagBuilding& b = inf.buildings[i];
            if (b.Type != BUILDING_ARROWTOWER || b.Percent < 100) continue;
            double tx = blockCenter(b.BlockDR), ty = blockCenter(b.BlockUR);
            double dPt = sqrt(dist2(p->DR, p->UR, tx, ty));
            double dEt = sqrt(dist2(en->DR, en->UR, tx, ty));
            if (dEt < 6.0 * s_bls && dPt > dEt) continue; // 该塔被敌军压制
            if (dPt < bd) { bd = dPt; tw = &b; }
        }
        if (tw) {
            double tx = blockCenter(tw->BlockDR), ty = blockCenter(tw->BlockUR);
            double dTw = sqrt(dist2(p->DR, p->UR, tx, ty));
            // 已在塔旁（2.5格内）就不再乱动，交给箭塔输出
            if (dTw > 2.5 * s_bls && inf.GameFrame - s_priestCmdFrame >= 15) {
                HumanMove(p->SN, tx, ty);
                s_priestCmdFrame = inf.GameFrame;
            }
        } else if (inf.GameFrame - s_priestCmdFrame >= 15) {
            // 没有可用箭塔：沿远离敌军方向撤退（原逻辑兜底）
            double ddr = p->DR - en->DR, dur = p->UR - en->UR;
            double len = sqrt(ddr * ddr + dur * dur);
            if (len < 1e-6) { ddr = 1.0; dur = 0.0; len = 1.0; }
            double tx = p->DR + ddr / len * 14.0 * s_bls;
            double ty = p->UR + dur / len * 14.0 * s_bls;
            clampDetail(tx, ty);
            HumanMove(p->SN, tx, ty);
            s_priestCmdFrame = inf.GameFrame;
        }
        return;
    }

    // 2) 敌军中等距离（25格内）：中止探图，回最近的箭塔待命
    if (en && dEn < 25.0 * s_bls) {
        const tagBuilding* tw = nearestBuilding(inf, BUILDING_ARROWTOWER,
                                                p->DR, p->UR, true);
        if (tw) {
            double tx = blockCenter(tw->BlockDR), ty = blockCenter(tw->BlockUR);
            double d = 3.0 * s_bls;
            if (p->NowState == HUMAN_STATE_IDLE &&
                dist2(p->DR, p->UR, tx, ty) > d * d &&
                inf.GameFrame - s_priestCmdFrame >= 15) {
                HumanMove(p->SN, tx, ty);
                s_priestCmdFrame = inf.GameFrame;
            }
        }
        return;
    }

    // 3) 无敌情：探图阶段（11000帧前；第二波战车弓兵会专门猎杀祭司，
    //    故留足安全余量）。跳过已探索的路点，逐点推进
    if (inf.GameFrame < 11000 && s_scoutIdx < SCOUT_NUM) {
        while (s_scoutIdx < SCOUT_NUM &&
               blockExplored(SCOUT_WAYPOINTS[s_scoutIdx][0],
                             SCOUT_WAYPOINTS[s_scoutIdx][1]))
            ++s_scoutIdx;
        if (s_scoutIdx < SCOUT_NUM) {
            double tx = blockCenter(SCOUT_WAYPOINTS[s_scoutIdx][0]);
            double ty = blockCenter(SCOUT_WAYPOINTS[s_scoutIdx][1]);
            double reach = 5.0 * s_bls;
            if (dist2(p->DR, p->UR, tx, ty) <= reach * reach) {
                ++s_scoutIdx;               // 已到达，转下一个路点
                s_scoutWpFrame = inf.GameFrame;
            } else {
                // 路点超时（1800帧没走到，可能隔海/被挡），跳过
                if (inf.GameFrame - s_scoutWpFrame > 1800) {
                    ++s_scoutIdx;
                    s_scoutWpFrame = inf.GameFrame;
                } else if (p->NowState == HUMAN_STATE_IDLE ||
                           inf.GameFrame - s_priestCmdFrame >= 60) {
                    HumanMove(p->SN, tx, ty);
                    s_priestCmdFrame = inf.GameFrame;
                }
            }
            return;
        }
    }

    // 4) 平时驻守：最近的箭塔旁（塔的射程就是保护圈）
    const tagBuilding* tw = nearestBuilding(inf, BUILDING_ARROWTOWER,
                                            p->DR, p->UR, true);
    if (tw && p->NowState == HUMAN_STATE_IDLE) {
        double tx = blockCenter(tw->BlockDR), ty = blockCenter(tw->BlockUR);
        double d = 3.0 * s_bls;
        if (dist2(p->DR, p->UR, tx, ty) > d * d &&
            inf.GameFrame - s_priestCmdFrame >= 15) {
            HumanMove(p->SN, tx, ty);
            s_priestCmdFrame = inf.GameFrame;
        }
    }
}

/*----------------------------------------------------------------------------
 * 5. 箭塔管理：空闲箭塔对射程内敌军自动开火
 *    注意：箭塔 Project >= 0 表示已有攻击目标，此时绝不能重复下令
 *    （重复下令会重置攻击动作，导致箭塔永远打不出伤害）
 *--------------------------------------------------------------------------*/
void UsrAI::manageTowers(const tagInfo& inf)
{
    for (size_t i = 0; i < inf.buildings.size(); ++i) {
        const tagBuilding& b = inf.buildings[i];
        if (b.Type != BUILDING_ARROWTOWER || b.Percent < 100) continue;
        if (b.Project >= 0) continue;   // 已有攻击目标

        // 指令冷却（防一帧多令）
        int last = -1000;
        map<int, int>::iterator it = s_towerCmdFrame.find(b.SN);
        if (it != s_towerCmdFrame.end()) last = it->second;
        if (inf.GameFrame - last < 10) continue;

        double tx = blockCenter(b.BlockDR), ty = blockCenter(b.BlockUR);
        const tagArmy* en = nearestEnemy(inf, tx, ty);
        if (!en) continue;
        double range = 8.0 * s_bls;     // 箭塔射程7格，留1格余量
        if (dist2(tx, ty, en->DR, en->UR) < range * range) {
            HumanAction(b.SN, en->SN);
            s_towerCmdFrame[b.SN] = inf.GameFrame;
        }
    }
}

/*----------------------------------------------------------------------------
 * 6. 军队管理：敌军接近祭司时全军优先拦截；否则就近攻击；
 *    无敌情时集结在市镇中心东南侧防守
 *--------------------------------------------------------------------------*/
void UsrAI::manageArmies(const tagInfo& inf)
{
    if (s_tcDR < 0) return;
    double gx = blockCenter(s_tcDR + 4), gy = blockCenter(s_tcUR + 4);
    double d = 3.0 * s_bls;

    // 护祭司：锁定离祭司最近的敌军（若其已进入祭司20格内）
    const tagArmy* priest   = findPriest(inf);
    const tagArmy* threat   = NULL;
    if (priest) {
        threat = nearestEnemy(inf, priest->DR, priest->UR);
        if (threat) {
            double pd = 20.0 * s_bls;
            if (dist2(priest->DR, priest->UR, threat->DR, threat->UR) > pd * pd)
                threat = NULL;          // 敌军离祭司还远，不触发护送
        }
    }

    for (size_t i = 0; i < inf.armies.size(); ++i) {
        const tagArmy& a = inf.armies[i];
        if (a.Sort == AT_PRIEST) continue; // 祭司单独管理

        if (!inf.enemy_armies.empty()) {
            if (a.NowState != HUMAN_STATE_IDLE &&
                a.NowState != HUMAN_STATE_WALKING) continue;

            // 指令冷却：同一单位15帧内不重复下令
            int last = -1000;
            map<int, int>::iterator it = s_armyCmdFrame.find(a.SN);
            if (it != s_armyCmdFrame.end()) last = it->second;
            if (inf.GameFrame - last < 15) continue;

            // 有可见敌军：优先拦截威胁祭司的敌军，否则就近攻击
            const tagArmy* target = threat;
            if (!target) target = nearestEnemy(inf, a.DR, a.UR);
            if (target) {
                HumanAction(a.SN, target->SN);
                s_armyCmdFrame[a.SN] = inf.GameFrame;
            }
        }
        else if (a.NowState == HUMAN_STATE_IDLE &&
                 dist2(a.DR, a.UR, gx, gy) > d * d) {
            // 无敌情：集结到市镇中心东南侧（敌方来向）
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

    // 首帧初始化：记录块边长和市镇中心位置
    if (s_tcDR < 0) {
        s_bls = BLOCKSIDELENGTH; // 从运行时配置读取
        const tagBuilding* tc = NULL;
        for (size_t i = 0; i < inf.buildings.size(); ++i) {
            if (inf.buildings[i].Type == BUILDING_CENTER) {
                tc = &inf.buildings[i];
                break;
            }
        }
        if (tc) { s_tcDR = tc->BlockDR; s_tcUR = tc->BlockUR; }
        else    { s_tcDR = 22; s_tcUR = 20; } // 兜底：地图默认市镇中心
    }

    // 累计新探索的地图块（供祭司探图使用）
    updateExplored(inf);

    s_builderSN = -1; // 每帧重置（由 manageBuild 设置）

    manageBuild(inf);           // 建造
    manageBuildingActions(inf); // 研发/造村民/练兵/升级
    manageFarmers(inf);         // 村民
    managePriest(inf);          // 祭司
    manageTowers(inf);          // 箭塔
    manageArmies(inf);          // 军队

    // 周期性状态输出（每600帧=24秒一次，便于调试观察）
    if (inf.GameFrame % 600 == 0) {
        const tagArmy* priest = findPriest(inf);
        DebugText(QString(
            "[AI] f=%1 meat=%2 wood=%3 stone=%4 pop=%5/%6 civ=%7 army=%8 farmer=%9 "
            "scout=%10/%11 priestHp=%12")
            .arg(inf.GameFrame).arg(inf.Meat).arg(inf.Wood).arg(inf.Stone)
            .arg(inf.Human_Num).arg(inf.Human_MaxNum)
            .arg(inf.civilizationStage).arg(armyCountNonPriest(inf))
            .arg((int)inf.farmers.size())
            .arg(s_scoutIdx).arg(SCOUT_NUM)
            .arg(priest ? priest->Blood : 0));
    }
}
