# C2BTOR 2.0

[English](README.md) · [简体中文](README.zh-CN.md)

## 1. C2BTOR framework

C2BTOR 是一个基于硬件模型检测的 C 程序验证框架。它通过 [CBMC](https://github.com/diffblue/cbmc) 前端将带有断言的 C 程序转换为 Goto-IR，再生成 BTOR2 状态迁移模型，交给不同的硬件模型检测器搜索反例或证明安全性质。

![C2BTOR 框架：C2Btor-dev 中的 CBMC 前端、Goto-IR 与 C2BTOR 编码生成 BTOR2；可选地转为 AIGER。反例经回放、回译和独立确认后报告 UNSAFE，完整无界证明后报告 SAFE。](docs/images/c2btor-framework.png)

图中的 **C2Btor-dev** 表示[开发仓库](https://github.com/westtide/C2Btor-dev)中的转换组件；C 前端仍来自 CBMC。仓库改名不会改变前端的技术来源。

**SAFE\*** 要求无界算法证明全部选中性质和模型边界义务；有界搜索无反例不代表 SAFE。图中的独立 validator 是单独的确认步骤，不能把 witness 文件生成成功当作独立验证成功。

## 2. 依赖与安装

本源码发布面向 **Linux x86-64**。转换器及构建目标为 **`c2btor`**，版本为 **`2.0.0`**，包含 **CBMC 6.11.0** 前端。本次同步来源为 `westtide/C2Btor-dev` 的提交 [`4e617cf2ea95c1e70f5b7598fdba04e4284dd215`](https://github.com/westtide/C2Btor-dev/commit/4e617cf2ea95c1e70f5b7598fdba04e4284dd215)。仓库提供源码；模型检测器需另行构建或安装。

- **构建**：C++17 编译器、CMake 3.16+、Make 或 Ninja、Flex、Bison、Git、Perl、Bash 和 `patch`。默认配置会下载并构建 MiniSat。
- **转换**：C 预处理器，例如 GCC。仅生成模型时无需模型检测器。
- **验证与 witness（可选）**：独立安装后端；witness 入口另需 Python 3.10+、PyYAML、Carat witness 版和配套 BtorSim。独立确认需另行配置 validator。

Ubuntu/Debian 示例，从仓库根目录运行：

```sh
sudo apt-get update
sudo apt-get install build-essential cmake ninja-build flex bison patch git perl python3-venv
git clone https://github.com/westtide/c2btor.git
cd c2btor
cmake -S . -B build -G Ninja -DCMAKE_BUILD_TYPE=Release
cmake --build build --target c2btor -j4
build/bin/c2btor --version
```

默认仅构建产品及必要依赖，不包含 JBMC。内存较小时降低 `-j4`；默认依赖下载需要网络。系统已有 MiniSat 头文件和库时，可在新的构建目录配置 `-Dsat_impl=system-minisat2`。

可选的转换器安装：

```sh
cmake --install build --component c2btor --prefix /path/to/install
```

该组件安装转换器、补全、中英文 README、图片和许可声明。完整 witness 工具链单独准备：

```sh
git submodule update --init --recursive checkers/carat
python3 -m venv .venv
.venv/bin/pip install -r scripts/requirements-witness.txt
```

`checkers/carat` 是固定版本的 **Carat 源码子模块**，不含预编译 checker；仅生成 BTOR2 时无需初始化。按 [Carat witness 版构建说明](https://github.com/westtide/carat-witness#build) 构建 Carat 和配套 BtorSim。验证入口会查找仓库构建目录及 `PATH`；也可通过 `C2BTOR`、`CARAT`、`BTORSIM` 环境变量指定工具。

## 3. 支持的硬件模型检测器

| 工具 | 输入路径 | 说明 |
| --- | --- | --- |
| [Carat witness 版](https://github.com/westtide/carat-witness) | BTOR2 | `c2btor-verify` 使用的后端，可产生 YAML 2.1 回译所需的标准反例。原版 Carat 不含这些 witness 扩展。 |
| [rIC3](https://github.com/gipsyh/rIC3) | BTOR2 / AIGER | IC3、BMC 等；为本发布所用的 rIC3 路径选择纯 BV 模型。 |
| [Pono](https://github.com/stanford-centaur/pono) | BTOR2 | 多种 SMT 模型检测算法；按工具官方说明选择 solver 与算法。 |
| [BtorMC](https://github.com/Boolector/boolector) | BTOR2 | 有界模型检测；无反例只覆盖所搜索的界限。 |
| [AVR](https://github.com/aman-goel/avr) | BTOR2 | 格式兼容后端；本次同步未独立验证其端到端 witness 路径。 |
| [SimpleCAR](https://github.com/lijwen2748/simplecar)、[ABC](https://github.com/berkeley-abc/abc) | BTOR2 → AIGER | 位级模型检测；使用纯 BV 编码，并先通过 `btor2aiger` 转换。 |

数组、属性数量和反例格式需与后端匹配。`array` / `mixed` 模型不能直接交给不支持数组的后端；其他兼容 BTOR2/AIGER 的检测器也可接入。

## 4. 使用参数与命令

### 转换带断言的 C 程序

```sh
mkdir -p work
cat > work/program.c <<'EOF'
extern unsigned __VERIFIER_nondet_uint(void);
int main(void)
{
  unsigned x = __VERIFIER_nondet_uint();
  __CPROVER_assert(x + 1U != 0U, "unsigned wrap");
}
EOF
build/bin/c2btor work/program.c --goto-btor2 --inline --32 \
  --array bv --goto-btor2-out work/model.btor2 \
  --goto-btor2-map-out work/model.map.json
```

ILP32 任务选择 `--32`，Linux LP64 任务选择 `--64`；它们描述 C 目标数据模型。模型与 map 必须使用不同文件，已有输出文件受到覆盖保护。可运行 `catbtor work/model.btor2` 检查语法和类型；parser 通过不等于证明程序安全。

### 参数说明

参数值用空格传入，不要同时传入正反开关或不同的重复表示值。

| 参数 | 含义与用途 |
| --- | --- |
| `--goto-btor2` | 启用 C 到 BTOR2 转换。 |
| `--goto-btor2-out FILE` / `--goto-btor2-map-out FILE` | 分别指定模型及 witness 源代码映射文件。 |
| `--inline` | 内联普通函数调用。 |
| `--32` / `--64` | 选择 C 目标数据模型 ILP32 / LP64。 |
| `--memory object` / `--memory global` | 对象独立存储或全局内存；默认 `object`。 |
| `--array bv` / `--array array` / `--array mixed` | BV、Array 或 Mixed 存储；默认 `bv`。Mixed 仅支持 object 内存。 |
| `--array-mixed-threshold-bits N` | Mixed 存储的对象位数阈值，默认 `2048`。 |
| `--goto-btor2-merge-bads` | OR 合并选中的源 bad；默认开启。用 `--goto-btor2-no-merge-bads` 关闭。 |
| `--goto-btor2-checks` | 显式插入所选 CBMC 检查；配合 `--bounds-check`、`--pointer-check`、`--div-by-zero-check` 等使用。 |
| `--goto-btor2-optimize-state` | 编码前优化并移除不可观察状态；默认开启。用 `--goto-btor2-no-optimize-state` 关闭。 |
| `--goto-btor2-no-array-optimizations` | 将 Array/Mixed 的数组优化恢复为原先需显式启用的行为，用于对照。 |
| `--memory-object-max-bytes N` | 显式限制对象容量；默认自动规划，容量不足时拒绝转换。 |
| `--goto-btor2-heap-objects K` | 对象存储槽限制；默认或 `0` 为自动推导，槽不足时拒绝转换。 |

转换默认不插入 CBMC 标准检查；源断言及标准 SV-COMP 错误函数调用成为性质。旧命令中的 `--no-standard-checks` 等选项在 BTOR2 模式下只保留为兼容开关。以当前 `build/bin/c2btor --help` 为准，不沿用旧版的 error-function、reach-only 或 no-heap-guards 命令。

### 调用模型检测器

按已安装工具选择一条路径检查上面的纯 BV 模型：

```sh
ric3 check work/model.btor2 portfolio
carat -a ic3 work/model.btor2
btor2aiger work/model.btor2 > work/model.aig
abc -c "read_aiger work/model.aig; pdr"
```

`btor2aiger` 由 [Btor2Tools](https://github.com/hwmcc/btor2tools) 提供，构建该工具时启用对应转换器。仅转换成功、BMC 无反例、UNKNOWN 或超时均不能作为 SAFE 证明。

### 生成 YAML 2.1 witness

准备实际调用 `reach_error` 的程序及性质文件：

```sh
cat > work/reach.c <<'EOF'
extern unsigned __VERIFIER_nondet_uint(void);
void reach_error(void) { __CPROVER_assert(0, "error reached"); }
int main(void)
{
  if(__VERIFIER_nondet_uint() == 10U) reach_error();
  return 0;
}
EOF
cat > work/reach.prp <<'EOF'
CHECK( init(main()), LTL(G ! call(reach_error())) )
EOF
.venv/bin/python c2btor-verify work/reach.c --property work/reach.prp \
  --data-model ILP32 --witness-output work/witness.yml \
  --keep-intermediates work/verify-run
```

witness 文件和中间产物目录必须尚不存在。该入口使用 object + Array，运行四个 Carat 配置；Unsafe 路径经 BtorSim 回放、回译后写出 YAML 2.1。它不自动调用独立 validator，需另行确认候选 witness。当前 Safe 路径写出的不变式为 `1`，不能当作独立安全证书。

完整接口见 `build/bin/c2btor --help` 和 `.venv/bin/python c2btor-verify --help`。

### 构建并运行聚焦测试

```sh
.venv/bin/pip install -r scripts/tests/requirements.txt
cmake -S . -B build-tests -G Ninja -Denable_cbmc_tests=ON \
  -DPython3_EXECUTABLE="$PWD/.venv/bin/python"
cmake --build build-tests -j4
ctest --test-dir build-tests --output-on-failure
```

包含 C2BTOR、C 前端与 GOTO-IR 的聚焦 C++ 测试及 Python/CLI/witness 检查。外部工具未就绪时，部分集成检查会跳过。转换或有限轨迹检查不替代无界证明。

## 5. 致谢与许可

**C2BTOR 基于 CBMC 构建。** 感谢 Daniel Kroening、Edmund Clarke、CBMC/CProver 作者及所有上游贡献者提供 C 前端、Goto-IR、目标机器配置与程序变换。参考 [CBMC 源码](https://github.com/diffblue/cbmc)及[官方文档](https://diffblue.github.io/cbmc/)。同时感谢 Carat、Btor2Tools、各模型检测器、witness validator 和其他依赖的作者与维护者。

源码保留 [LICENSES/](LICENSES/) 中的 C2BTOR BSD-4-Clause、CBMC 和各第三方声明。根目录 [LICENSE](LICENSE) 和 [LICENSE.c2btor](LICENSE.c2btor) 继续保存发布仓库已有声明，不替代各组件自己的许可条件。

This product includes software developed by the C2BTOR contributors.

> This product includes software developed by Daniel Kroening,
> Edmund Clarke,
> Computer Science Department, University of Oxford,
> Computer Science Department, Carnegie Mellon University.
