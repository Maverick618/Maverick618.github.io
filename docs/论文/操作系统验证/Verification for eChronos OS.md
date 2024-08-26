# Controlled Owicki-Gries Concurrency: Reasoning about the Preemptible eChronos Embedded Operating System

> A non-interference VC asserts that some assertion in task X is preserved by some statement from task Y . Since most assertions will be guarded by AT=X, and most statements will by AT=Y , many of these VC’s will have antecedent False.

这段脚注的意思是：一个非干扰验证条件（VC）断言，任务X中的某些断言被任务Y中的某些语句所保持。由于大多数断言将由AT=X保护，大多数语句将由AT=Y保护，因此许多这样的验证条件的前提为假。

换句话说，这段脚注指出，验证条件的前提条件通常是任务X的某个状态变量（AT=X）和任务Y的某个状态变量（AT=Y）不相等。在这种情况下，验证条件的前提条件为假，因此整个验证条件将被认为是正确的（因为前提为假则整个逻辑表达式为真）。这减少了需要手动检查的验证条件的数量，从而简化了验证过程​​。

但涉及共享变量时，情况就会有所不同了。
