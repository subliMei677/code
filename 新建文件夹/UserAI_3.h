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

    /*================ 自定义成员函数（v3 修订版） ================
     * 目标：及格线强化（存活 + 升铜器）→ 为完整胜利版打底
     * v3 修订（针对第二轮测试 5 问题 + 6 条新策略）：
     *   [问题1] 村民持续生产到 36 人（不再限制开局 2400 帧/12 人），
     *           人口将满自动补房屋，适配不同地图的开局差异
     *   [问题2] 祭司探路重写：只在波次间隙的“探路窗口”外出，
     *           波前 1500 帧回箭塔下躲避；移动指令 90 帧冷却 +
     *           ins_ret 失败核对 + 300/600 帧无位移检测 → 拉黑路点，
     *           彻底修复“指令反复刷屏但人不动”
     *   [问题3] 箭塔成簇建造（市镇中心东南 3~7 格内 3 座，间距 3+ 格，
     *           内核并无箭塔间距限制），祭司躲避点即塔簇
     *   [问题4] 伐木配额 6 人（研发木材加工后降为 4 人）；
     *           市场建成后立即研发木材加工（采集率 0.02→0.22）
     *   [问题5] 资源占用去重：农田 1 人/块、树木/浆果/石/金等
     *           2~3 人/个（按内核 WorkObjectSN 实时统计占用）
     *   [策略1] 第一波(6000帧)前不造兵，资源优先箭塔+市场+靶场
     *   [策略2] 第二波(13500帧)前囤 800 食物升铜器，再点科技
     *   [策略3] 第一波后(~7500帧)造兵营 → 棍棒兵+弓箭手，
     *           铜器后升级兵营科技（阔剑兵）
     *   [策略4] 村民生产至接近人口上限
     *   [策略5] 第二波前研发箭塔强化（攻+1 射程+1）
     *   [策略6] 8 块农田，1 人 1 田耕种
     *===============================================================*/
    void manageBuild(const tagInfo& gameInfo);           // 建造管理（双在途槽位）
    void manageBuildingActions(const tagInfo& gameInfo); // 研发/造村民/练兵/升级时代
    void manageFarmers(const tagInfo& gameInfo);         // 村民：逃跑 > 上交 > 配额分工采集
    void managePriest(const tagInfo& gameInfo);          // 祭司：遇袭逃塔 > 庇护窗口 > 探路窗口 > 驻守
    void manageTowers(const tagInfo& gameInfo);          // 箭塔自动攻击
    void manageArmies(const tagInfo& gameInfo);          // 军队防守（含护祭司、警戒圈）
};


/*##########YOUR CODE BEGINS HERE##########*/



/*##########YOUR CODE ENDS HERE##########*/
#endif // USRAI_H
