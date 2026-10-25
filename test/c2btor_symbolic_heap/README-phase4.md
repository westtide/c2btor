# Phase 4: certified word cells and symbolic-slot state reduction

The default-off switch is --goto-btor2-symbolic-heap-compact. It requires the
symbolic heap Array path. Constant capacities and bounded Mixed storage keep
their existing layouts. See IMPLEMENTATION.md for the call chain and boundaries.

The final frozen binary SHA256 is
9b8afb66766c923638df9671ad328f5cade957373607ca93860018ae20aa7138.
The full goto-btor2 suite passes 1821 assertions in 95 cases, including cast-LHS
fact loss, ASSERT conditions not acting as premises, and narrow-offset fallback.
The compact-off binary matches the parent on all 120 configuration statuses and
all 90 successful model hashes. Native on/off have 90 parser passes/30 explicit
rejections; explicit BV Array fallback has 34 passes/6 rejections. No new source
bad, property-count mismatch or constraint increase occurs in common successes.

Original ILP32 nsqm-iff, same no-LBE/map configuration:

| Metric | Before compact | After compact |
| --- | ---: | ---: |
| Dynamic identities | 2 | 2 |
| Active data Arrays | 2 | 2 |
| Total data Array states, including seeds | 4 | 2 |
| Total size states, including seeds | 4 | 2 |
| Total states | 35 | 27 |
| PC locations | 111 | 111 |
| Nodes | 2276 | 1266 |
| Array read / write nodes | 64 / 64 | 8 / 8 |
| Source bad / auxiliary bad | 1 / 0 | 1 / 0 |
| Existing source-library abort constraints | 2 | 2 |

The certificate reports eight aligned 64-bit accesses. Its data sorts are
Array(BV29, BV64); byte pointers still have full BV32 offsets plus hidden tags,
and size snapshots remain BV32. Sizes/elements are not materialized. N stays
a nondeterministic saved state, three loops retain PC backedges, and two supplied
N values on the variable-extent source use the same model hash.

The final finite ledger reports 120 configurations: 102 supplied-prefix passes
and 18 expected conversion rejections. Nonzero initial Array states are supplied
explicitly, with independent frame-zero read observations checking byte/word
seeds. Calloc's zero helper stays zero. Mixed byte aliases keep byte backing;
small bounded Mixed calloc keeps its original backend. These are finite replay
observations, not SAFE/FALSE backend verdicts. Backend checking is NOT_RUN.

The final 770-record cohort excludes the four requested recursive programs.
All 3064 conversion/parser runs for the 766 eligible programs completed:
Array/Mixed each 741 pass, pure BV 553 pass, BV with explicit dynamic Array
fallback 691 pass. Compared with the previous optimization snapshot, Array,
Mixed and BV fallback each add 138 converted cases; no previous success is lost.
Source hashes match the previous cohort. Details and all failures are in
lab1-final-results.json, FAILED_CASES.md and failed-cases.csv.

The goal of converting every eligible case is not achieved: Array/Mixed retain
18 automatic-lifetime refusals, five automatic/VLA capacity refusals, one finite
allocation-count refusal and one missing selected property. BV fallback adds
50 independent logical-array packing refusals. Those boundaries are not bypassed.

Outputs, exact commands, parser logs, models and maps remain under results/.
The six initial T8 symbolic-mixed conversion records made before its range was
stabilized are superseded by phase4-on-mixed-final. Earlier whole-cohort runs
with incomplete FILE compatibility declarations are also superseded. Final
source/tool hashes and model/parser statuses are bound in the ledgers.
