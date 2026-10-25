# C2BTOR 维护与验证记录

记录日期：2026-10-25。机器可读统计见 [validation.json](validation.json)。

## 计划与交付范围

| 项目 | 本次结果 |
|---|---|
| 1. 开发仓库与历史 | 保留开发仓库历史；仓库重命名按用户要求暂缓 |
| 2. 上游同步 | 合并 CBMC develop `8fcda333650440a60d3a054552a7ad318255b95d`，前端版本更新为 6.11.0 |
| 3. 构建与内容精简 | 默认构建仅包含 C2BTOR 的依赖图；保留必要生成工具与聚焦测试 |
| 4. 参数和优化 | 显式拒绝冲突选项；保护输出文件；保留 Array/Mixed 默认管线，BV 默认启用表示无关的状态裁剪 |
| 5. 文档 | README 仅列用户接口；AGENTS 提供构建、运行、测试与结果解读 |
| 6. 许可证 | 原始许可集中于 LICENSES/；C2BTOR 贡献使用 BSD-4-Clause；保留第三方独立许可 |
| 7. 发布 | 以开发仓库 PR 交付；本次不合并 main、不更新公开发行仓库 |
| 8. 主页 | 完成 Pages 方案评估；本次不启用站点或创建账号 |

## 上游关系与后续同步

本次开发基线为 `58db665462f3f7aec6e1363d0e7a16b812380f5f`，与上游的共同祖先为
`844c8e63f5a53d2b3299197e2e13699a2d35b807`。合并保留了 Git 父提交关系，
包含 parser、库模型、GOTO-IR、确定性编号、函数参数求值顺序和相关修复。

核心冲突保留 C2BTOR 产品名、转换入口及显式安全检查策略，同时接入上游的
不可达函数移除等变换。已移除的 Java 前端、旧文档和工具没有作为运行依赖恢复。

新克隆的开发仓库可以按以下顺序同步：

```sh
git remote add upstream https://github.com/diffblue/cbmc.git
git fetch upstream develop
git switch -c sync/cbmc-YYYY-MM-DD
git -c merge.renames=false merge --no-commit --no-ff upstream/develop
```

若 upstream 已存在，直接 fetch。先检查本地工作树并保存基线结果，再处理合并。
逐项审查核心代码冲突；已移除模块和上游新加的无关文件也需要复查。
不要机械恢复所有删除。确认产品依赖图、前端、GOTO-IR、BTOR2 和 witness 测试后提交。

公开的 westtide/c2btor 具有独立源码快照历史，不适合直接合并整条开发历史。
开发 PR 合并并通过 CI 后，应另建发行 PR，将已验证的源码树更新到公开仓库，
保留公开仓库既有历史和全部许可声明。

## 构建与回归

本次环境为 Ubuntu 24.04 / GNU 13.3.0 / CMake 3.28 / Python 3.12。
执行了默认依赖图构建及启用聚焦测试的构建。保留的 converter 和 file_converter
属于 C 内建库的构建期生成工具，不是额外发布的产品。

保留 regression/cbmc-library 的库模型测试和 regression/test.pl：内部 C/C++ 库的
编译检查还会核对每个模型函数的测试清单。干净 CI 首轮发现该依赖曾在精简中被删除，
而本地增量 stamp 掩盖了它；已恢复这组必要测试，并在无 stamp 目录重跑库检查。
这些 fixtures 的完整功能回归可在该目录中用 ../test.pl -c /absolute/path/c2btor 运行；
它不属于本次聚焦 CTest 的 187 个 C++ 用例统计。

```sh
python3 -m venv .venv
.venv/bin/pip install -r scripts/tests/requirements.txt
cmake -S . -B build -G Ninja -Denable_cbmc_tests=ON \
  -DPython3_EXECUTABLE="$PWD/.venv/bin/python"
cmake --build build -j4
ctest --test-dir build --output-on-failure
```

本地结果：

| 检查 | 结果 |
|---|---|
| C++ 聚焦单元测试 | 187 个用例，6,721 条断言通过 |
| Python / CLI / witness | 58 项，53 通过、5 项外部集成检查跳过 |
| BV 状态裁剪开关对照 | 44/44 转换、catbtor、有限轨迹检查通过 |
| 原始基线与候选，三种表示、32/64 位 | 138/138 通过 |
| 复杂 Array/Mixed 数组和块合并 | 120/120 通过 |
| 产品安装与许可 | 可执行文件、补全及许可证安装成功；仓库外转换和 catbtor 检查通过 |
| 运行包脚本 | bash -n 语法检查通过；未执行完整 Carat 运行包构建 |
| 无 stamp 的库模型检查 | C/C++ 检查通过；项目自有 __builtin_bzero 功能回归通过 |

原始基线的旧测试曾因缺少 schema 依赖、过时的默认开关预期及 fixture 缺少
kind 字段而失败。已补齐声明的测试依赖和 fixture，未改写 witness 的生产判定。
同时修复了测试中 sys.modules 恢复导致 LibYAML 重导入的问题。

跨版本有限对照中，旧转换器显式启用 `--goto-btor2-optimize-state`；
新转换器使用对应默认值，避免把旧版巨大无用 BV 对象的容量拒绝当作轨迹不一致。
复杂数组用例显式传入与默认管线对应的已有开关，使旧测试框架的结构断言可复核。

前端回归来自本次上游的 qualified __auto_type、命名地址空间、常量复合初始化、
跨翻译单元不完整数组；见 test/frontend。复合初始化样例仅将 assert.h 替换为
相同性质的 __CPROVER_assert，避免依赖宿主机 multilib 头文件。
这些检查验证前端类型处理；新增前端语法并不自动扩大 BTOR2 的支持子集，
例如部分嵌套静态聚合初始化仍会明确返回 Unsupported。

## BV 优化测量

使用同一个上游合并后转换器，对 22 个 ILP32/LP64 固定输入配置分别关闭和开启
表示无关的状态裁剪；两侧都保持纯 BV，没有引入 Array 存储。

| 总量 | 关闭 | 开启 |
|---|---:|---:|
| 状态数 | 270 | 152 |
| BV 状态位数 | 6,336 | 4,684 |
| 数值节点 | 8,908 | 7,585 |
| 模型字节数 | 174,192 | 152,997 |
| 转换耗时合计（秒） | 2.295337 | 2.291331 |

这些短样例的耗时接近测试框架的 0.1 秒轮询粒度，不能据此声称速度提升。
模型规模下降和有限轨迹检查支持启用这一部分优化；没有将原生 Array 摘要或
符号堆存储变换作为 BV 默认值。完整 Carat 求解耗时和外部 witness validator
未在本次本地验证中运行；有限前缀也不证明无界等价或 C 程序安全。

## 许可证和打包

LICENSES/CBMC-BSD-4-Clause.txt 与开发基线中的 CBMC 原文保持一致。
LICENSES/C2BTOR-BSD-4-Clause.txt 声明 C2BTOR 自有代码的许可，源码保留
SPDX 声明。第三方许可原文见 LICENSES/ 及对应组件目录。DownloadProject、MiniSat、
Catch2、Carat 和测试 schema 沿用各自许可；不统一改成 BSD。
产品安装包含原始声明、项目声明和第三方许可。运行包脚本还收集实际构建依赖的
原始许可证，缺失则失败。完整 Carat 运行包构建未在本次执行。

## PR #7 评论复核

根据 [维护者评论](https://github.com/westtide/cbmc/pull/7#issuecomment-6392383998) 更新：

| 检查项 | 处理 |
|---|---|
| src/cbmc/btor2_demo.h 与目录清理 | 删除 demo 的头文件、实现及 CLI 入口；移除引用旧 CBMC 工具路径的 dist 脚本和 distribution.xml；保留生产入口与仍被引用的代码 |
| src/goto-btor2.zip | 删除旧源码归档，避免与实际源码并存 |
| src/solvers/floatbv | 完整保留，与本 PR 上游合并后的树一致 |
| src/analyses | 完整保留抽象解释和优化实现，与本 PR 上游合并后的树一致 |
| src/goto-analyzer | 从上游合并后的版本恢复；提供显式构建目标，默认产品构建不增加独立分析工具；已运行常量分析/简化并将结果交给 C2BTOR 和 catbtor 检查 |
| .github/workflows/c2btor.yml | 保留 Linux 聚焦回归，增加 Ubuntu arm64、macOS arm64、Windows x86_64 转换器构建；工作流要求四种产物通过安装、三种表示转换和许可检查后才上传 Artifacts |
| cmake 两个 DownloadProject 文件 | DownloadProject.cmake 是调用模块，DownloadProject.CMakeLists.cmake.in 是 configure_file 使用的子项目模板；两者共同执行一次依赖获取，不是两套下载器 |
| scripts/build_svcomp.sh | 保留 Linux 完整运行包脚本；补齐 Perl 预检、提前检查项目许可、统一由 CMake 管理 MiniSat HTTPS URL/校验，并在运行包 README 中保留必要致谢 |

Carat 的固定版本 setup.sh 会自行切换到脚本目录，原私有克隆的调用方式可保留。
打包脚本新增输入安全检查测试，覆盖缺少许可时提前失败和保留已有输出；完整 Carat 运行包构建仍需单独执行，不能把这些预检视为完整运行包验收。

## GitHub Pages 评估

建议先在公开仓库使用 **westtide.github.io/c2btor/**：现有仓库即可管理静态主页，
内容可以直接复用安装说明、示例、论文和发行链接。等项目需要独立身份时，
再考虑 **c2btor.github.io**；它要求名为 c2btor 的用户或组织，以及
c2btor.github.io 仓库，不是 westtide 账号下任意仓库都能占用的地址。

依据 [GitHub Pages 官方说明](https://docs.github.com/en/pages/getting-started-with-github-pages/what-is-github-pages)，
项目站点的默认地址为 owner.github.io/repositoryname，用户/组织站点为 owner.github.io。
本次只评估方案；未创建组织、变更仓库设置或发布网页。
