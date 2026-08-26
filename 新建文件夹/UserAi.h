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

    /*================ 自定义成员函数（初版及格线 AI） ================
     * 目标：存活10分钟 + 升级到铜器时代（及格线）
     * 具体：经济(村民采集/生产) -> 建筑(兵营/市场/靶场/房屋/箭塔)
     *       -> 科技(研发箭塔、囤800食物升铜器) -> 军事(训练棍棒兵防守)
     *       -> 保命(祭司与村民遇敌自动撤离)
     *===============================================================*/
    void manageBuild(const tagInfo& gameInfo);           // 建造管理
    void manageBuildingActions(const tagInfo& gameInfo); // 研发/造村民/练兵/升级时代
    void manageFarmers(const tagInfo& gameInfo);         // 村民：逃跑 > 上交 > 采集分工
    void managePriest(const tagInfo& gameInfo);          // 祭司保命
    void manageArmies(const tagInfo& gameInfo);          // 军队防守
};


/*##########YOUR CODE BEGINS HERE##########*/



/*##########YOUR CODE ENDS HERE##########*/
#endif // USRAI_H
