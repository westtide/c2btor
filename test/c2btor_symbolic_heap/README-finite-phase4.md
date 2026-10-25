# Phase 4 finite execution evidence

`finite-phase4-results.json` passes with **120 compact configurations: 102
finite regression passes, 18 expected rejections, and zero discrepancies**.
Array/Mixed contribute 80 configurations (68/12); BV with explicit Array
fallback contributes 40 (34/6). The final frozen converter SHA256 is
`9b8afb66766c923638df9671ad328f5cade957373607ca93860018ae20aa7138`.

The 21-case manifest includes the original source references, symbolic calloc,
and a non-singleton mixed-width companion. Each accepted case checks that its
source ASSERT actually executes, with both fixed nondet ports and ports that
change after their call frames. The new calloc/mixed sources also pass all 12
target/encoding configurations using the P3 parent binary without compact;
source hashes, observed values, source ASSERT execution counts and source
failure counts match their compact counterparts.

For nsqm, all three encodings report two active data Array states, two total
Array states, two dynamic size states, no zero helper, and a successful word64
certificate with eight accesses. Each cell has 64 bits and a 29-bit index,
while byte offsets retain all 32 target bits. The two supplied small/large N
traces use the same source and model hash for each target/encoding pair. The
N=1 source failure still precedes source-abort constraint invalidation; only
constraint-valid prefixes are scored.

The broad-range mixed-byte companion fails word certification and retains
byte8 Array cells. The original singleton mixed case keeps its old encoding.
Symbolic calloc conservatively uses byte cells, with one dynamic data/size
state and one separately counted initialized zero Array helper on the Array
path. Its address-taken library alloc_size object is a separate static BV
object, not an additional heap slot. Small bounded Mixed/BV calloc keeps its
existing packed representation. At supplied n=3, untouched first/last words
are zero; writing first=9 leaves last=0 and size=24.

Every Array input and every no-init Array state at `#0` receives the same
repeated 0x3d byte pattern. Init-constrained zero helpers are excluded. Four
independent read(index0) observations confirm actual frame0 values: byte
states contain 0x3d, word states contain 0x3d3d3d3d3d3d3d3d, and zero helpers
contain 0. These are explicit chosen arbitrary values, not a general rule
that malloc contents are zero. This initial-state coverage was added after
the earlier P3 runs; their original records remain unchanged.

The ledger contains 204 compact fixture traces, 24 same-backend constant-size
UB counterpart traces, 24 parent new-case traces and four initial-seed
observation traces: 256 finite simulations. Source/model/map and trace hashes
are checked. Raw outputs are in `results/finite-phase4-final`,
`results/finite-phase4-final-bv-fallback`, their two new-case off directories,
and `results/finite-phase4-seed-checks`. Initial P4 exploration is superseded.

Only parser/type acceptance, explicit finite prefixes, rejection checks and
storage contracts were tested. No solver/model checker, C SAFE/UNSAFE result,
or unconditional standard-C equivalence proof is claimed. The summary can be
recreated without running a verification tool:

```sh
python3 test/c2btor_symbolic_heap/summarize_phase4.py
```
