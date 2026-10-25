# C2Btor optimization regressions and metrics

Run the harness from the repository root. It calls only the converter, official
`catbtor` parser/type checker, and finite `btorsim` simulator. It never calls a
model checker. A passing regression checks the specified concrete input prefix;
it is not an unbounded C safety proof.

The committed fixtures cover unsigned wrap and narrowing, both branch paths,
loop exit reachability, ASSERT before a later failing ASSUME, independent nondet
calls and sharing one call result, array initialization, both pointer alias
choices, and writes followed by direct and indirect reads. Each ordinary case
has an intentional final failing assertion named `optimization-reached`. The
harness requires that marker and rejects any other assertion failure in the
valid prefix. The prefix case requires its earlier failure to precede the first
constraint violation.

`unused-capacity` runs only on ILP32. With state optimization disabled it must
reject the unused 400,000,000-byte array for the exact representation-limit
reason and leave no model. This is a passed *case* with `model_passed=false` and
`status=expected_conversion_error`. With optimization enabled, conversion,
parser and finite replay must pass, and no `unused` state may remain.

```sh
python3 scripts/check_c2btor_optimizations.py \
  --before build/bin/c2btor \
  --after-arg=--goto-btor2-optimize-state \
  --catbtor /path/to/catbtor --btorsim /path/to/btorsim \
  --configs bv,array,mixed --workers 2 \
  --output-dir test/c2btor_optimizations/results/phase1-regressions
```

Use `--before` and `--after` to select separate executable snapshots. Repeat
`--before-arg`, `--after-arg`, or `--common-arg` once per command-line token. For
example, an include path needs `--common-arg=-I --common-arg=/path/to/include`.
Use fresh output directories for each run. `--case-filter` accepts a regular
expression, and repeated filters match with OR. `--architectures 32` restricts
finite regressions; benchmark architectures always come from task YAML.

```sh
python3 scripts/check_c2btor_optimizations.py --mode metrics \
  --before /path/to/baseline/c2btor --after build/bin/c2btor \
  --after-arg=--goto-btor2-optimize-state \
  --catbtor /path/to/catbtor --configs bv,array,mixed \
  --records /path/to/Lab1_btor_v8_records.csv \
  --aiob-headers /path/to/linux_compatible_headers \
  --output-dir test/c2btor_optimizations/results/phase1-lab1
```

`--records` deduplicates its `file_path` column and selects that exact dataset
set. The local manifest contains 773 tasks; the historical records select 770.
`benchmark-selection.json` records selected tasks, hashes, and all additional
manifest tasks. `--cases-file` accepts relative source or task YAML paths and
intersects any records selection. Add `--limit 2` for a small metrics smoke run.
Dataset aliases `ob` and `oa` map to `--array bv` and `--array array`; they are
never sent as array-encoding CLI values. The optional aiob header adaptation
adds Linux/i386 declarations for `loop-industry-pattern/aiob_4*` without changing
source bytes.

Metrics conversions omit source maps to avoid counting witness observation
nodes. They record state count/BV bits, array states, instruction positions and
PC positions from converter logs, distinct literal PC entry guards, numeric
node lines, read/write operations, model bytes, command status and elapsed time.
The count of numeric nodes includes sorts and declaration/root lines. Summaries
keep errors, timeouts and limits distinct and compare only successful paired
models. Regression model metrics explicitly indicate that map observations are
included. Simulator-only models append named aliases for mapped source-property
conditions and constraints; original model roots are unchanged.

Every run keeps commands, converter/parser/simulator logs, source/tool/model
hashes, original models/maps, fixed traces, VCD observations, JSON summaries and
CSV records. Outputs under `results/` are ignored. The default limits are 60 s
for each conversion, 30 s for parser and simulator, a sampled 4 GiB process-tree
RSS limit, and 128 MiB per conversion output file. Process RSS sampling needs
process-table access; use `--memory-gib 0` explicitly only when running without
that measurement. `--max-model-mib 0` explicitly disables the file-size limit.

`cases-witness.json` adds a separate phase 1 mapping smoke with two nondet calls
and copied values. Run it with Python packages from
`scripts/requirements-witness.txt`:

```sh
python3 scripts/check_c2btor_optimizations.py \
  --regression-manifest test/c2btor_optimizations/cases-witness.json \
  --before /path/to/frozen/c2btor \
  --after-arg=--goto-btor2-optimize-state \
  --catbtor /path/to/catbtor --btorsim /path/to/btorsim \
  --output-dir test/c2btor_optimizations/results/phase1-witness-smoke
```

The smoke uses the existing `export` command to bind source/model hashes, finds
the target using the supplied fixed inputs, trims the trace at that frame, and
runs `translate` and offline `lint`. It requires both original nondet result
states in the map, distinct return waypoints constrained to 5 and 9, and one
target. The `sat`/`b0` lines in its generated BTOR2 witness declare that supplied
trace in the required file format; they are not a solver verdict. Its metadata
records `model_checking_run=false`, `solver_run=false` and
`cpachecker_run=false`.
