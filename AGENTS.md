# C2BTOR 使用速查

本说明供用户和 Agent 在新环境中构建、转换、验证与复现测试。安装依赖和完整用户参数见 [README.md](README.md)。

## 选择入口

只生成模型时运行转换器：

```sh
build/bin/c2btor program.c --goto-btor2 --inline --32 \
  --array array --goto-btor2-out model.btor2
```

需要验证和 YAML 2.1 witness 时，在准备好 README 中的 Carat 和 Python 环境后运行：

```sh
./c2btor-verify program.c --property unreach-call.prp --data-model ILP32
```

32 位任务使用 ILP32 / `--32`，64 位任务使用 LP64 / `--64`。这描述 C 目标，不是宿主机位数。单独转换默认 object + BV；验证入口使用 object + Array；Mixed 仅支持 object 存储。

模型和 map 使用不同文件；witness 输出路径不能已有文件。保留验证中间产物时使用 `--keep-intermediates NEW_DIR`。

## 构建与测试

从仓库根目录运行：

```sh
python3 -m venv .venv
.venv/bin/pip install -r scripts/tests/requirements.txt
cmake -S . -B build -G Ninja -Denable_cbmc_tests=ON \
  -DPython3_EXECUTABLE="$PWD/.venv/bin/python"
cmake --build build -j4
ctest --test-dir build --output-on-failure
```

不启用 `enable_cbmc_tests` 时，默认只构建产品及必要依赖。启用后包含 C2BTOR、C 前端和 GOTO-IR 的聚焦 C++ 测试，以及 CLI、解析、回译和 YAML 测试。部分外部 BtorSim/witness 集成测试需要另行准备工具，跳过项会在日志中显示。

regression/cbmc-library 保存内部库模型的必要测试清单及 fixtures，构建期库检查依赖它。

保留的 GOTO 分析工具可按需构建：`cmake --build build --target goto-analyzer -j4`。
例如使用 `build/bin/goto-analyzer --constants --simplify simplified.gb program.c` 进行常量分析和 GOTO-IR 简化。该独立驱动不参与默认转换器构建或产品安装；`src/analyses` 的核心分析库仍是转换器依赖。

如需比较转换器版本，使用 `scripts/check_c2btor_optimizations.py --help`。它需要 catbtor 和 btorsim，只比较固定输入有限轨迹；不运行无界模型检查。输入样例位于 `test/c2btor_optimizations/` 和 `test/c2btor_symbolic_heap/`。

## 读取结果和排查错误

- 参数冲突会报错；不要同时传入正反开关或不同的重复表示值。
- Unsupported 表示任务超出当前表示能力；保留原始任务和错误信息以便复现。
- catbtor 成功只说明语法和类型可接受。
- 分别记录转换、模型检查、反例回放、witness 生成和外部 validator 的结果。
- Unknown、超时和有界无反例没有安全结论。当前 Safe witness 的不变式 `1` 也不能作为独立安全证书。

前端新接受的 C 语法不一定都已有 BTOR2 编码；遇到明确 Unsupported 时，应依据实际输出描述支持范围。

上游来源、回归范围、许可证和主页评估见 [维护记录](docs/maintenance.md)。
