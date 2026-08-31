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

    /*================ 自定义成员函数（v5.1 修订版） ================
     * 目标：稳过三波防守 → 进攻阶段：侦察定位敌方基地 → 攒兵一波总攻
     *
     * v5.1 核心改动（相对 v5.0）：
     *   [1] 第三波防守强化：兵力目标 12近战+12远程；箭塔与军队目标
     *       优先级加入投石车（射程10格>塔7/8格，是失守主因）。
     *   [2] 第三波结束(25000帧)后完全停止建塔/重建，采石配额归零，
     *       资源转入进攻经济（采金3人供阔剑兵，伐木6人供复合弓）。
     *   [3] 祭司转化三级优先级：攻击祭司者 > 方阵兵 > 投石车 > 最近敌。
     *   [4] 农田上限 8→10，农田之间强制间隔≥1个空格。
     *   [5] 箭塔强化的50石预留从"铜器后"提前到"时代开始升级时"。
     *   [6] 兵营/靶场/马厩选址锚点改为初始箭塔（塔群），兵力快速协防。
     *   [7] 军队攻击最优先：WorkObjectSN==祭司 的敌军。
     *   [8] 进攻模块 manageAttack：马厩训侦察骑兵探明敌方基地；
     *       攒足20兵一波总攻（先打敌军，建筑按 塔>军事建筑>经济建筑
     *       >市镇中心 的顺序）；存活<8撤回落位重新攒兵，循环进攻。
     *
     * 早期版本要点沿用：
     *   - 箭塔围绕开局预置箭塔建造；建造失败坐标永久拉黑
     *   - 建造点下达前校验整块占地已探索+平地+无重叠
     *   - 祭司三塔质心驻守；食物采集优先级 浆果>羚羊/大象>农田
     *   - 烂尾建筑续建；远程存放建筑去重；农田锚定谷仓偏移5格
     *===============================================================*/
    void manageBuild(const tagInfo& gameInfo);           // 建造（螺旋选址+坐标拉黑）
    void manageBuildingActions(const tagInfo& gameInfo); // 研发/造村民/练兵/升级时代
    void manageFarmers(const tagInfo& gameInfo);         // 村民：逃跑>上交>分工采集>开视野
    void managePriest(const tagInfo& gameInfo);          // 祭司：转换>治疗>探路>驻守
    void manageTowers(const tagInfo& gameInfo);          // 箭塔自动攻击
    void manageArmies(const tagInfo& gameInfo);          // 军队防守（含护祭司、警戒圈）
    bool priestMoveTo(const tagInfo& gameInfo, const tagArmy* priest,
                      int tdr, int tur, int cooldown);   // 祭司移动辅助（带冷却）
    bool priestMoveToDetail(const tagInfo& gameInfo, const tagArmy* priest,
                            double tx, double ty, int cooldown); // 祭司移动到精确坐标（带冷却）
    void manageAttack(const tagInfo& gameInfo);          // v5.1 进攻模块（侦察/攒兵/总攻）
};


/*##########YOUR CODE BEGINS HERE##########*/



/*##########YOUR CODE ENDS HERE##########*/
#endif // USRAI_H
