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

    /*================ 自定义成员函数（v2 修订版） ================
     * 目标：存活10分钟 + 升级到铜器时代（及格线）
     * v2 修订（针对首轮测试反馈）：
     *   1. 祭司探图：无敌情时沿固定路点探索地图（11000帧前）
     *   2. 祭司遇袭：撤向最近的箭塔寻求庇护，而非乱跑
     *   3. 军队护祭：敌军接近祭司时优先拦截其附近敌军
     *   4. 箭塔自动开火：空闲箭塔对射程内敌军下令攻击
     *   5. 村民防发呆/防指令刷屏：指令冷却 + 结果核对 +
     *      失败目标拉黑 + 目标轮换 + 卡住强制挪位
     *===============================================================*/
    void manageBuild(const tagInfo& gameInfo);           // 建造管理
    void manageBuildingActions(const tagInfo& gameInfo); // 研发/造村民/练兵/升级时代
    void manageFarmers(const tagInfo& gameInfo);         // 村民：逃跑 > 上交 > 采集分工
    void managePriest(const tagInfo& gameInfo);          // 祭司：逃向箭塔 > 探图 > 驻守
    void manageTowers(const tagInfo& gameInfo);          // 箭塔自动攻击
    void manageArmies(const tagInfo& gameInfo);          // 军队防守（含护祭司）
};


/*##########YOUR CODE BEGINS HERE##########*/



/*##########YOUR CODE ENDS HERE##########*/
#endif // USRAI_H
