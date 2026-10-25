# 符号尺寸堆：第二阶段

新增 `--goto-btor2-symbolic-heap-arrays`，默认关闭，要求第一阶段开关和 object 内存。原生 Array 的符号分配槽使用固定的偏移索引域与一个字节元素，容量只在已有 size 状态中保存，不按容量物化元素，也不建立容量大小的位图。

每个 fresh 身份保留同一个 data/live/size/readonly 后备。真正需要符号存储的事件可能到达任意 fresh 槽，因此所有动态槽统一使用这个后备。区间为单一常量的容量继续走原路径；Mixed 的可认证小上界仍按既有阈值选择 BV。

读写由现有对象号分发。符号槽对完整访问范围使用 W+1 位 `uext(off)+bytes <= uext(size_snapshot)`，先扩展再加，不新增 live 门控、bad 或 constraint。malloc 未写数据仍任意且稳定；calloc 的常零数组和自动对象 reset 沿用已有实现。

旧的分配次数认证完全保留。第三阶段尚未改变内部指针，所以超出现有 signed offset 表示的容量仍明确拒绝；本阶段不能声称原始 ILP32 nsqm 已能转换。没有完整容量区间时，按整个机器字节数域检查表示能力，不能用人为阈值限制输入。

验证：96 组 C 配置在开关前后均为 78 个转换与官方 parser 成功、18 个明确 Unsupported，无新转换失败。关闭第二阶段开关的所有成功模型与第一阶段冻结版本 hash 一致；成功模型都是一个源 bad、零 constraint。详见 `phase2-results.json` 的逐例状态、PC、节点和 read/write 对比。

全部 `[goto-btor2]` 测试通过：1651 assertions / 78 test cases。新增固定域/逐对象后备、Mixed 小对象阈值，以及 little/big endian 下最后合法访问、one-past 总化、free 元数据与既有 live-independent 数据行为的固定轨迹回归。UB 轨迹仅检查编码既有规则，不是 C SAFE 证据；模型检查与后端 SAFE/FALSE/UNKNOWN 未运行。

主要修改：`object_memory.cpp`、`heap_model.{h,cpp}`、编码选项与 CLI、`unit/goto-btor2/symbolic_heap.cpp`；动态 copy/reset/lowering 算法没有另行重构。
