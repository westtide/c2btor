# C2BTOR conversion regression tests / 转换回归

Run from the repository root after building `build/bin/c2btor` on Linux x86-64.
Install Btor2Tools and any required backend separately. Defaults for string
tool arguments use PATH; arguments typed as paths should be absolute.
Use each script's `--help` for its exact dependencies and case selection.

在仓库根目录运行。外部工具单独安装；字符串工具参数默认从 PATH 查找，
路径类型参数请传绝对路径。最终输出目录应尚不存在，避免覆盖旧实验。

```sh
run=$(mktemp -d /tmp/c2btor-regression.XXXXXX)
python3 regression/goto-btor2/check_properties.py \
  --c2btor "$PWD/build/bin/c2btor" \
  --catbtor "$(command -v catbtor)" --output "$run/properties"
```

`check_properties.py` checks conversion/parser behavior for property
preservation and selection, including rejected input. It does not run a
solver or validate C witnesses.

| Script | Purpose / 用途 |
| --- | --- |
| `check_properties.py` | Source assertions, selected error calls, merge modes and auxiliary properties / 属性保留与选择。 |
| `check_heap_rules.py` | Allocation, lifetime, aliases and copy semantics; requires BtorMC or rIC3 / 堆规则。 |
| `check_array_encoding.py`, `check_object_memory.py` | Storage representations and behavior / 存储编码。 |
| `check_auto_capacity.py`, `check_array_capacity.py` | Capacity planning and boundaries / 容量及边界。 |
| `check_object_copy.py` | Object and byte-copy behavior / 对象复制。 |
| `check_float_lowering.py` | Floating-point circuits and replay / 浮点电路及回放。 |
| `check_model_contract.py` | Hidden model obligations and result classification / 模型契约。 |
| `check_witness_translation.py` | Hash binding, replay, translation and optional CPAchecker validation / 反例回译。 |

Keep conversion success, parser success, solver verdict, BtorSim replay and
CPAchecker confirmation separate. A bounded no-counterexample result is not
an unbounded SAFE proof. Memory validity and model limits are not source
unreach-call counterexamples. See the root README for usage and result interpretation.

`check_constant_callback.py` and `check_symbol_heap.py` accept `RIC3` and
`CATBTOR` environment overrides. Other scripts expose tool arguments.
`test/tools/` retains additional batch tools; external benchmark datasets
are not bundled. The small C examples in `test/corner_case_c_bugs/` are
retained without old generated models, logs or witnesses.
