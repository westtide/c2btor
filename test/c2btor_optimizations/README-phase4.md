# Phase 4 array-block regressions

The converter flag is `--goto-btor2-array-blocks`. Both variants use state
optimization, logical arrays, and scalar blocks, so only array-block encoding
changes. No solver, model checker, or CPAchecker is invoked.

Merged logical element operations are limited to integer and Boolean leaves.
Enum/float leaves and whole-array aggregate operations retain ordinary
instruction boundaries and their existing conversion behavior. Physical memory,
pointer/byte aliases, nondeterministic calls, and ASSUME also remain boundaries.
This conservative merge eligibility does not introduce a conversion rejection.

Fifteen scenarios yield 180 finite runs over ILP32/LP64, BV/Array/Mixed, and flag
off/on. Supplied indices cover same-index read-after-write (7) and another index
(0), two writes with last value 9, both guarded branch joins (18/12), two ASSERT
snapshots separated by another store, a 70-iteration array loop (2,485), captured
2D VLA stride after its source dimension changes, VLA declaration reentry in a
two-iteration loop, and independent array roots (7/9 yielding 79), with a newly
stored third-array value used as a nested subscript. Every read
uses an explicitly initialized element. Assertion boundaries must keep each
snapshot tied to the store version at that execution point.

The supplied scalar read temporary `observed` must have no persistent state
when array blocks are enabled, retain a 32-bit mapped value, and gain no free
input replacing its state. The supplied value observations are checked against
their exact expected numbers and compared across flags. Explicit logical-array
metadata continues to verify rank, element width, backend, and latched dynamic
dimension capture. These two explicitly marked VLA fixtures allow persistent
dimension/data states to be pruned only with state optimization and certified
array-block metadata. The retained DECL storage input must still have the exact
Array index/element sorts or packed BV width chosen by the backend. All original
phase 2/3 fixture expectations remain strict.

The VLA sources write a complete row before the dimension scalar changes, then
read/modify/write another row and require the first row to remain independent.
This detects a wrong stride even if both a later write and read use that same
wrong stride. The repeated declaration captures lengths 2 then 3 on loop entry;
the second iteration's third-column sentinel must survive the second-row store.
Later changes of the dimension scalar to 1 must not alter the captured stride.
Array-block metadata must declare current storage versions; selected
array fixtures require an ASSERT merged with preceding operations, and the
two-snapshot source requires two such terminal ASSERTs. Scalar block partition,
singleton nondet/ASSUME, and terminal-ASSERT checks apply to both variants.

Five existing phase 2 cases are reused: address escape and byte aliases must
keep canonical byte storage and observe indirect mutations; eligible pointer
identity and generic fixed-NULL pointer fallbacks must preserve exact mapped
pointer-integer bits; Boolean array stores/initializers must normalize values
to 0/1 within merged blocks. Pointer values are compared between flags without
hardcoding object tags. Whole-array nondet and unsupported aggregate operations
that cannot be expressed as ordinary C array assignment are covered by raw
public-GOTO units, preserving boundaries and existing rejection/property
behavior. The finite nondet-array unit also retains untouched value 23 after
another element is written to 7 in all three backends.

The witness source stores the two supplied nondet values 5/9, copies a later
array read, and has one conditional `reach_error` when the sum is 14. Twelve
runs must export with matching hashes, replay the supplied prefix, translate
two return events followed by the target, and pass offline lint. The BTOR
witness header labels supplied finite simulation, not a solver SAT result.

```sh
python3 scripts/check_c2btor_optimizations.py \
  --regression-manifest /path/to/cases-phase4.json \
  --before /path/to/frozen/c2btor --frames 2048 \
  --common-arg=--goto-btor2-optimize-state \
  --common-arg=--goto-btor2-logical-arrays \
  --common-arg=--goto-btor2-scalar-blocks \
  --after-arg=--goto-btor2-array-blocks \
  --catbtor /path/to/catbtor --btorsim /path/to/btorsim \
  --output-dir test/c2btor_optimizations/results/phase4-regressions
```

Use `cases-witness-phase4.json` separately with the same common/after flags.
The completed frozen unit run and exact 770-task conversion/parser matrix are
reported below. Common-success metrics and newly converted models are recorded
separately in the JSON ledger.

## Frozen phase 4 results

The frozen converter SHA256 is
`e774ee3f997faca5c2ea80be738fa98339230d2732083807570a928721ea81db`.
The final `[goto-btor2]` unit run passed 1,582 assertions in 73 cases. All 180
finite conversion/parser/simulation runs, 48 exact value pairs, and 12
hash-bound witness export/translate/offline-lint runs passed. The 90 finite
and six witness pairs had no bad-count mismatch or constraint-count increase.

An initial run had twelve harness errors because its two VLA checks required
persistent DIM/data states after all uses had become block local. That run is
marked superseded in `results/phase4-reviewed-regressions`; the converter hash
did not change. The final run uses fixture-specific permission, concrete
storage-input sort checks, and strengthened cross-row/reentry assertions.

The exact 770-record matrix completed all 4,620 conversion/parser attempts,
using common phase 1/2/3 flags, three workers, a 4 GiB process-tree RSS limit,
a 128 MiB model-file limit, and 60/30-second conversion/parser limits. Maps were
omitted. The converter accepts `--array bv`, `--array array`, or `--array mixed`.
Dataset labels `ob`/`oa` mean BV/Array; they are optional `--configs` aliases in
this harness, not converter CLI values. Counts are conversion/parser outcomes,
not SAFE/UNSAFE results.

| Encoding | Raw 770 off pass / fail | Raw 770 on pass / fail | Nonrecursive 766 off pass / fail | Nonrecursive 766 on pass / fail |
|---|---:|---:|---:|---:|
| BV | 554 / 216 | 554 / 216 | 553 / 213 | 553 / 213 |
| Array | 604 / 166 | 604 / 166 | 603 / 163 | 603 / 163 |
| Mixed | 604 / 166 | 604 / 166 | 603 / 163 | 603 / 163 |

There were no newly converted tasks, new failures, bad-count mismatches, or
constraint-count increases. The common-success cohort therefore equals all
successful on models per encoding. Its structural changes are:

| Encoding | States off → on | PC positions off → on | Numeric nodes off → on | Bytes off → on | Byte reduction |
|---|---:|---:|---:|---:|---:|
| BV | 5,377 → 5,109 | 28,245 → 25,654 | 1,340,147 → 1,333,132 | 29,763,358 → 29,589,443 | 0.58% |
| Array | 5,981 → 5,560 | 29,863 → 26,624 | 1,844,785 → 1,835,304 | 42,074,624 → 41,835,049 | 0.57% |
| Mixed | 5,984 → 5,563 | 29,863 → 26,624 | 1,841,286 → 1,831,805 | 41,985,621 → 41,745,927 | 0.57% |

State counts decreased 4.98% in BV and 7.04% in Array/Mixed; PC positions
decreased 9.17% and 10.85%. Active PC entries became 25,571/26,541/26,541,
and equality guards 26,299/27,386/27,386. Numeric nodes decreased about 0.52%.
Bitvector state bits decreased by 8,794 in BV and 13,667 in Array/Mixed; the
very large packed-state bit total makes BV’s relative decrease about 0.0002%.
Array-state counts stayed 0/558/505, read operations 0/4,825/2,608, and write
operations 0/10,153/9,892. Instruction positions stayed 107,500/110,680/110,680.
Byte reductions are small, and the measurements do not show fewer emitted
array read/write operations.

All failures remained conversion rejections: 138 allocation-byte-capacity,
5 runtime-object-byte-capacity, 21 automatic-object-lifetime, 1 allocation-count,
and 1 no-selected-source-property case per encoding; BV additionally has 50
logical-array packed-width/bound rejections.
`array-examples/sanfoundry_43_ground.i` deliberately remains property free.
The four recursive sources are excluded only from the secondary 766 cohort;
the three additional local-manifest tasks remain outside the exact 770 set.
Conversion of all 770 targets is still incomplete.

The largest on model remains
`loop-industry-pattern/aiob_4.c.v+nlh-reducer.c` in every encoding:

| Encoding | Phase 3 on = phase 4 off = phase 4 on bytes | Size rank / successful models | Share of on-model bytes |
|---|---:|---:|---:|
| BV | 5,872,705 | 1 / 554 | 19.85% |
| Array | 19,287,780 | 1 / 604 | 46.10% |
| Mixed | 19,176,428 | 1 / 604 | 45.94% |

This task receives no additional phase 4 size reduction. Earlier large-tail
preparation `b912ef` is separate from the four optimization stages; these
off/on measurements do not attribute the previously reported 452/468 MB sizes
to phase 4.

All 2,310 phase 4-off source/YAML/status pairs and all 1,762 successful off-model
hashes match phase 3-on exactly under identical flags without maps. A separate
read-only audit confirmed those comparisons and rehashed all 3,524 corresponding
model files. All 770 primary source and YAML hashes agree across both variants,
current files, and phases 1/2/3. All 14 fixture-source hashes, all 3,524 current
phase 4 benchmark model hashes, and frozen converter/parser/simulator/harness
hashes were checked without drift.

[phase4-results.json](phase4-results.json) records full metric totals, failure
taxonomies, exact flags, cases, hashes, and the independent compatibility audit.
Ignored evidence is in `results/phase4-final-regressions`,
`results/phase4-final-witness-smoke`, and `results/phase4-final-lab1-full`,
including `source-hashes.json`, `analyze_phase4.py`, and
`off-switch-compatibility-independent.json`. No model checker, solver, or
CPAchecker was run. Parser acceptance, fixed-input finite prefixes, and offline
witness lint do not prove unbounded safety or semantic equivalence.
