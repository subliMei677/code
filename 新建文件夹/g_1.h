#ifndef USRAI_H
#define USRAI_H

#include "ai.h"
#include <unordered_map>

extern tagGame tagUsrGame;
extern ins UsrIns;
/*##########DO NOT MODIFY THE CODE ABOVE##########*/

class UsrAI:public AI
{
public:
    UsrAI(){this->id=0;}
    ~UsrAI(){}

private:
    void processData() override;
    tagInfo getInfo(){return tagUsrGame.getInfo();}
    int AddToIns(instruction ins) override
    {
        UsrIns.lock.lock();
        ins.id=UsrIns.g_id;
        UsrIns.g_id++;
        UsrIns.instructions.push(ins);
        UsrIns.lock.unlock();
        return ins.id;
    }
    void clearInsRet() override
    {
        tagUsrGame.clearInsRet();
    }
    /*##########DO NOT MODIFY THE CODE IN THE CLASS##########*/

    /*================ 自定义成员函数（v4.3 修订版） ================
     * 目标：祭司转化制胜 → 三塔火力保护祭司 → 第二波前兵营靶场达标造兵
     *
     * v4.3 核心改动（相对 v4.2）：
     *   [1] 祭司转化强化：冷却就绪即转化最近敌军；射程放开到12格；
     *       射程外主动走近到10格转化；转化后立刻返回三塔质心。
     *   [2] 祭司躲避点改为三塔质心：所有已建成箭塔的几何中心，确保
     *       始终处于最多箭塔的交叉火力下；箭塔索敌优先级改为"攻击
     *       祭司的敌军优先"（WorkObjectSN == 祭司SN）。
     *   [3] 第一波后节奏修正：箭塔强化科技一下令即解除资源冻结，
     *       立刻开始兵营造兵；硬性配额门控——棍棒兵<4时只造棍棒兵，
     *       弓箭手<2时只造弓箭手，达标后才解锁阔剑兵/复合弓兵。
     *
     * 早期版本要点沿用：
     *   - 箭塔围绕开局预置箭塔建造；建造失败坐标永久拉黑
     *   - 所有建造点下达前校验整块占地已探索+平地+无重叠
     *   - 升铜器前不采金、不采石；食物采集优先级：浆果 > 羚羊/大象 > 农田
     *   - 市场+靶场建成且食物≥800 立即升铜器
     *   - 村民永不发呆：无本职资源时依次转木材→食物→(铜器后石/金)→开视野
     *   - 烂尾建筑续建；远程存放建筑去重；农田锚定谷仓偏移5格
     *
     * 后期策略扩展点：各 manage* 函数均按游戏阶段分支，
     * 后期进攻/防守策略可在对应函数中增量添加。
     *===============================================================*/
    void manageBuild(const tagInfo& gameInfo);           // 建造（螺旋选址+坐标拉黑）
    void manageBuildingActions(const tagInfo& gameInfo); // 研发/造村民/练兵/升级时代
    void manageFarmers(const tagInfo& gameInfo);         // 村民：逃跑>上交>分工采集>开视野
    void managePriest(const tagInfo& gameInfo);          // 祭司：转换>治疗>探路>驻守
    void manageTowers(const tagInfo& gameInfo);          // 箭塔自动攻击
    void manageArmies(const tagInfo& gameInfo);          // 军队防守（含护祭司、警戒圈）
    void manageLions(const tagInfo& gameInfo);           // v5.0 狮子处理（村民猎杀）
    bool priestMoveTo(const tagInfo& gameInfo, const tagArmy* priest,
                      int tdr, int tur, int cooldown);   // 祭司移动辅助（带冷却）
    bool priestMoveToDetail(const tagInfo& gameInfo, const tagArmy* priest,
                            double tx, double ty, int cooldown); // 祭司移动到精确坐标（带冷却）
};


/*##########YOUR CODE BEGINS HERE##########*/



/*##########YOUR CODE ENDS HERE##########*/
#endif // USRAI_H
