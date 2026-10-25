# Phase 1 evidence

The final comparison in `phase1-results.json` passes. The reviewed phase4
snapshot, final phase1 converter with the flag off, and the same final converter
with `--goto-btor2-symbolic-heap` each ran 96 configurations: 32/64-bit targets
as listed in the manifest, across object Array/BV/Mixed.

Each group has 78 conversion/parser passes and 18 explicit Unsupported results:
Array 27/5, BV 24/8, Mixed 27/5. No status changes occurred. Every accepted model
is byte-identical across baseline/off/on: model hashes, node/state counts, PC
positions, read/write counts, and property counts match. Every accepted model has
one source bad, one mapped source property, and zero constraints. Current source
hashes match all three recorded groups.

The enabled maps preserve typed 32/64-bit allocation byte expressions, identify
allocation-time size snapshots, and state that CFG-path allocation counting is
unchanged. Expected event bounds match storage slots, including three distinct
slots for the bounded loop's one malloc site. Maps contain no heap proof
obligation, heap property, or freeze-on-violation policy.

Existing representation limits remain: original ILP32 nsqm-iff and the large
32-bit offset cases reject due to the old signed offset range; huge 64-bit BV
capacities reject due to bit-vector representation width; the unbounded malloc
loop rejects due to allocation count. These are intended phase1 boundaries.
The additional serialization boundary fixtures still use the existing compact
pointer encoding at this phase; later wide-offset support must explicitly
handle or reject them.

Raw commands, logs, models/maps, results and frozen binaries are in ignored
`results/baseline-final`, `results/phase1-final-off`, and
`results/phase1-final-on`. Earlier exploratory output is superseded. All runs
used 20s conversion and 10s parser timeouts with a 64MiB per-file limit. This
macOS sandbox does not permit ps-based RSS sampling or lowering RLIMIT_DATA;
there is no recorded peak RSS or memory limit.

This evidence covers conversion, parser/type acceptance, structural contracts,
and compatibility. No finite simulator, solver, or model checker was invoked;
no C safety verdict is claimed.

The report is reproducible after creating fresh recorder output directories:

```sh
python3 test/c2btor_symbolic_heap/compare_phase1.py
```

最终 C 回归共 96 组（32/64 位 × 三编码，按 fixture 支持架构过滤）：旧冻结版本、当前开关关闭和开启均为 78 个转换/parser 成功、18 个明确 Unsupported。全部 78 个成功模型的 hash、状态、节点、PC、bad 和 constraint 均完全一致；成功模型都是一个源 bad、零 constraint。
