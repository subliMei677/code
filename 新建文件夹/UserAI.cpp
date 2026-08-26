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
 * 初版 AI —— 目标：及格线（存活10分钟 + 升级到铜器时代）
 *
 * 策略概要：
 *   1. 经济：村民按 3:2 分工采集食物/木材；开局前1.6分钟持续造村民到12人；
 *            可见食物枯竭时用市场补农田
 *   2. 建筑：兵营(125木) -> 市场(150木) -> 靶场(150木)（满足升铜器的
 *            “2个工具时代建筑”前置）-> 房屋(30木,按人口) -> 2座箭塔(各150石,
 *            用光初始300石) ；建造位置从市镇中心向外的固定候选序列中取，
 *            失败自动换下一个位置
 *   3. 科技：谷仓一次性研发“箭塔解锁”(50食)；市镇中心在市场+靶场建成后
 *            囤够800食物立即升级铜器时代(60秒)
 *   4. 军事：兵营持续训练棍棒兵(50食/27秒)，第一波(6000帧)前6个、
 *            第二波(13500帧)前12个、之后16个；无敌人时集结在市镇中心
 *            东南侧（敌方来向），发现敌军就近攻击
 *   5. 保命：祭司(死亡即失败)敌军12格内就逃跑，平时驻守市镇中心西北侧；
 *            村民敌军5格内逃离
 *
 * 敌方进攻节奏（地图预置，不会补充）：
 *   第一波 ~6000帧(4分钟)：2斧头兵+1弓箭手
 *   第二波 ~13500帧(9分钟)：+方阵兵/阔剑兵/复合弓兵/战车弓兵，战车弓兵优先猎杀祭司
 *   第三波 ~21000帧(14分钟)：约10个铜器单位+2投石车（及格线只需活到10分钟）
 *
 * 注意：processData 每帧调用，所有跨帧状态都用 static 文件级变量保存；
 *       列表每帧会被打乱，一切以 SN 为准，不依赖下标。
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
static map<int, int>  s_lastFleeFrame; // 单位SN -> 上次逃跑指令帧（控制指令频率）

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

/* 按分工找最近可采资源：
 * 食物=浆果/羚羊/象（不招惹狮子），木材=树；无食物时可兜底己方农田 */
static int nearestResourceSN(const tagInfo& inf, double dr, double ur, char role)
{
    int sn = -1;
    double bd = 1e18;
    for (size_t i = 0; i < inf.resources.size(); ++i) {
        const tagResource& r = inf.resources[i];
        if (r.Cnt <= 0) continue;
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

    // 找离建造点最近的空闲村民
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
        if (b.Project != ACT_NULL) continue; // 忙碌中

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
 *--------------------------------------------------------------------------*/
void UsrAI::manageFarmers(const tagInfo& inf)
{
    double fleeR = 5.0 * s_bls;

    for (size_t i = 0; i < inf.farmers.size(); ++i) {
        const tagFarmer& f = inf.farmers[i];
        if (f.FarmerSort != FARMERTYPE_FARMER) continue;

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

        // 本帧已被派去建造的村民不再派采集任务
        if (f.SN == s_builderSN) continue;

        if (f.NowState != HUMAN_STATE_IDLE) continue;

        // 2) 手上有资源 -> 就近上交（浆果食物交谷仓，木/石/金/猎肉交仓库）
        if (f.Resource > 0) {
            int wantType = (f.ResourceSort == HUMAN_GRANARYFOOD)
                           ? BUILDING_GRANARY : BUILDING_STOCK;
            int depot = -1;
            double bd = 1e18;
            for (size_t k = 0; k < inf.buildings.size(); ++k) {
                const tagBuilding& b = inf.buildings[k];
                if (b.Type != wantType || b.Percent < 100) continue;
                double d = dist2(f.DR, f.UR,
                                 blockCenter(b.BlockDR), blockCenter(b.BlockUR));
                if (d < bd) { bd = d; depot = b.SN; }
            }
            if (depot >= 0) { HumanAction(f.SN, depot); continue; }
            // 找不到对应建筑就落到另一种（谷仓/仓库至少应有一个）
            wantType = (wantType == BUILDING_GRANARY) ? BUILDING_STOCK : BUILDING_GRANARY;
            for (size_t k = 0; k < inf.buildings.size(); ++k) {
                const tagBuilding& b = inf.buildings[k];
                if (b.Type != wantType || b.Percent < 100) continue;
                double d = dist2(f.DR, f.UR,
                                 blockCenter(b.BlockDR), blockCenter(b.BlockUR));
                if (d < bd) { bd = d; depot = b.SN; }
            }
            if (depot >= 0) { HumanAction(f.SN, depot); continue; }
        }

        // 3) 手空 -> 按分工就近采集（无食物可采时食物工先去伐木）
        char role = farmerRole(f.SN);
        int sn = nearestResourceSN(inf, f.DR, f.UR, role);
        if (sn < 0 && role == 'F') sn = nearestResourceSN(inf, f.DR, f.UR, 'W');
        if (sn >= 0) HumanAction(f.SN, sn);
    }
}

/*----------------------------------------------------------------------------
 * 4. 祭司管理：祭司死亡=直接失败，保命高于一切
 *--------------------------------------------------------------------------*/
void UsrAI::managePriest(const tagInfo& inf)
{
    const tagArmy* p = findPriest(inf);
    if (!p) return; // 祭司不在（已死亡或不可见），无能为力

    double fleeR = 12.0 * s_bls; // 大于敌方单位视野，先敌发现先敌撤退
    const tagArmy* en = nearestEnemy(inf, p->DR, p->UR);
    if (en && dist2(p->DR, p->UR, en->DR, en->UR) < fleeR * fleeR) {
        int last = -1000;
        map<int, int>::iterator lf = s_lastFleeFrame.find(p->SN);
        if (lf != s_lastFleeFrame.end()) last = lf->second;
        if (inf.GameFrame - last >= 15) { // 祭司逃跑反应更频繁
            double ddr = p->DR - en->DR, dur = p->UR - en->UR;
            double len = sqrt(ddr * ddr + dur * dur);
            if (len < 1e-6) { ddr = 1.0; dur = 0.0; len = 1.0; }
            double tx = p->DR + ddr / len * 14.0 * s_bls;
            double ty = p->UR + dur / len * 14.0 * s_bls;
            clampDetail(tx, ty);
            HumanMove(p->SN, tx, ty);
            s_lastFleeFrame[p->SN] = inf.GameFrame;
        }
        return;
    }

    // 无威胁：驻守市镇中心西北侧（远离敌方来向的相对安全位）
    if (p->NowState == HUMAN_STATE_IDLE) {
        double sx = blockCenter(s_tcDR - 4), sy = blockCenter(s_tcUR - 4);
        double d = 3.0 * s_bls;
        if (dist2(p->DR, p->UR, sx, sy) > d * d)
            HumanMove(p->SN, sx, sy);
    }
}

/*----------------------------------------------------------------------------
 * 5. 军队管理：见敌就近攻击；无敌情时集结在市镇中心东南侧防守
 *--------------------------------------------------------------------------*/
void UsrAI::manageArmies(const tagInfo& inf)
{
    if (s_tcDR < 0) return;
    double gx = blockCenter(s_tcDR + 4), gy = blockCenter(s_tcUR + 4);
    double d = 3.0 * s_bls;

    for (size_t i = 0; i < inf.armies.size(); ++i) {
        const tagArmy& a = inf.armies[i];
        if (a.Sort == AT_PRIEST) continue; // 祭司单独管理

        if (!inf.enemy_armies.empty()) {
            // 有可见敌军：空闲或正在行军的单位就近攻击
            if (a.NowState == HUMAN_STATE_IDLE || a.NowState == HUMAN_STATE_WALKING) {
                const tagArmy* en = nearestEnemy(inf, a.DR, a.UR);
                if (en) HumanAction(a.SN, en->SN);
            }
        }
        else if (a.NowState == HUMAN_STATE_IDLE &&
                 dist2(a.DR, a.UR, gx, gy) > d * d) {
            // 无敌情：集结到市镇中心东南侧（敌方来向）
            HumanMove(a.SN, gx, gy);
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

    s_builderSN = -1; // 每帧重置（由 manageBuild 设置）

    manageBuild(inf);           // 建造
    manageBuildingActions(inf); // 研发/造村民/练兵/升级
    manageFarmers(inf);         // 村民
    managePriest(inf);          // 祭司
    manageArmies(inf);          // 军队

    // 周期性状态输出（每600帧=24秒一次，便于调试观察）
    if (inf.GameFrame % 600 == 0) {
        DebugText(QString(
            "[AI] f=%1 meat=%2 wood=%3 stone=%4 pop=%5/%6 civ=%7 army=%8 farmer=%9")
            .arg(inf.GameFrame).arg(inf.Meat).arg(inf.Wood).arg(inf.Stone)
            .arg(inf.Human_Num).arg(inf.Human_MaxNum)
            .arg(inf.civilizationStage).arg(armyCountNonPriest(inf))
            .arg((int)inf.farmers.size()));
    }
}