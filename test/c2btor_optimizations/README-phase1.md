# Stage 1: property dependencies and state cleanup

Switch: `--goto-btor2-optimize-state` (off by default). Typed integer constants and pure irrelevant storage are simplified before capacity/lifetime planning. GOTO and ASSUME conditions remain roots, so loops that affect reachability remain. ASSERT never supplies a propagation premise. Unknown side effects and aliases are retained. Pointer/string programs conservatively skip the prepass to preserve the original object identity namespace; dependency pruning still runs.

Generated graph pruning starts from bad/constraint/output and requested map roots, and follows state init/next dependencies. Original numeric IDs remain valid with gaps. Requested maps preserve executed/value observations and nondet result states; ordinary conversions omit unrequested witness outputs.

Validation: 288 assertions in 31 unit cases, 138 finite regression checks (135 parser/simulation passes and 3 expected off rejections), and 12 hash-bound export/translate/lint round trips. No model checker or CPAchecker ran.

The exact 770 historical tasks were converted with all three object-memory encodings, on and off. Each configuration remains at **554 conversions/parser passes and 216 conversion errors**; there are no new conversion failures, bad-count changes, or increases in constraint count. After excluding four explicit recursive cases, there are 553 passes and 213 errors among 766 tasks. The remaining failure categories per encoding are 138 allocation-byte capacities, 55 runtime-object capacities, 21 lifetime certificates, one allocation-count bound, and one task with no selected source property.

Totals below compare the same 554 successful tasks; PC positions count planned blocks. Read/write counts refer to native BTOR2 Array operations.

| Encoding | States off → on | PC positions off → on | Nodes off → on | read/write off → on | MiB off → on |
|---|---:|---:|---:|---:|---:|
| bv | 12861 → 5526 | 30942 → 30775 | 2194470 → 1477176 | 0/0 → 0/0 | 47.99 → 31.50 |
| array | 12890 → 5120 | 30942 → 30775 | 3001416 → 2234524 | 24043/18888 → 22889/18774 | 66.81 → 49.37 |
| mixed | 12877 → 5139 | 30942 → 30775 | 2995429 → 2231774 | 20613/18450 → 20531/18450 | 66.67 → 49.30 |

Machine-readable counts, switches, tool hash, exact command and limitations are in [phase1-results.json](phase1-results.json). Full local commands, source/model hashes, models, maps and logs are in the ignored evidence directories recorded there. Parser/type checks and concrete simulation prefixes do not establish unbounded safety or equivalence.
