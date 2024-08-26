### TCB中的信号
```c++
typedef struct { // 任务控制块（TCB）的数据结构
    // ...
#ifdef LOSCFG_KERNEL_CPUP
    OsCpupBase      taskCpup;           /**< task cpu usage 任务的CPU使用率*/
#endif
    INT32           errorNo;            /**< Error Num 错误编号*/
    UINT32          signal;             /**< Task signal 任务信号*/
    sig_cb          sig;
    // ...
} LosTaskCB;
```
每一个tcb中都有一个signal和一个sig，sigs是一个信号控制块，用来管理信号的。其结构体定义如下：
```c++
typedef struct {
    sigset_t sigFlag;		///< 不屏蔽的信号集
    sigset_t sigPendFlag;	///< 信号阻塞标签集,记录那些信号来过,任务依然阻塞的集合.即:这些信号不能唤醒任务
    sigset_t sigprocmask;   ///< Signals that are blocked | 任务屏蔽了哪些信号
    sq_queue_t sigactionq;	///< 信号捕捉队列					
    LOS_DL_LIST waitList;	///< 待链表,上面挂的是等待信号到来的任务, 查找OsSchedTaskWait(&sigcb->waitList, timeout, TRUE)理解						
    sigset_t sigwaitmask; /*! Waiting for pending signals   | 任务在等待哪些信号的到来 */
    siginfo_t sigunbinfo; /*! Signal info when task unblocked   | 任务解锁时的信号信息  */
    SigInfoListNode *tmpInfoListHead; /*! Signal info List */
    unsigned int sigIntLock;///< 信号中断锁
    void *sigContext; ///< 信号上下文
    unsigned int count;///< 信号数量
} sig_cb;
```
`sigFlag`应该是这个任务收到的信号集合。
