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

    /*================ 自定义成员函数（v4 前期策略版） ================
     * 目标：稳定扛过第一波 → 尽快升铜器 → 第二波前兵营靶场就位造兵
     *
     * v4 修复的 11 项问题（相对 v3）：
     *   [1] 新箭塔围绕"开局预置箭塔"螺旋就近建造，不再远离初始塔
     *   [2] 祭司只向"已探索块"移动，探路目标由探索边界(前线)动态生成；
     *       失败/无位移的块自动拉黑换点，彻底解决"下令但不动"
     *   [3] 建造点下达前校验整块占地已探索+平地+无重叠；
     *       失败坐标永久拉黑，绝不重试同一坐标
     *   [4] 升铜器前不采金不采石（石料仅为第3座箭塔临时征用）
     *   [5] 食物采集优先级：浆果 > 羚羊/大象 > 农田
     *   [6] 市场+靶场建成且食物≥800 立即升铜器（含兜底重试）
     *   [7] 靶场作为升铜器前置更早建好；兵营第一波后即建，
     *       富余食物提前造兵，保证第二波前有兵
     *   [8] 祭司新增：转换敌军（冷却完毕即发）+ 治疗友军（血量最低）
     *   [9] 升铜器前村民恰好12人、不多造房屋；升铜器后扩至24人、
     *       补房屋并研发采集科技提速
     *  [10] 除"解锁箭塔"外所有科技仅铜器时代研发；升级前资源
     *       优先建市场/靶场等二级建筑满足升级条件
     *  [11] 村民反发呆：无资源可采时依次转木材→食物→石金→
     *       去探索边界开视野，永不空站
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
    bool priestMoveTo(const tagInfo& gameInfo, const tagArmy* priest,
                      int tdr, int tur, int cooldown);   // 祭司移动辅助（带冷却）
};


/*##########YOUR CODE BEGINS HERE##########*/



/*##########YOUR CODE ENDS HERE##########*/
#endif // USRAI_H
