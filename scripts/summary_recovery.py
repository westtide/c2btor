# SPDX-License-Identifier: BSD-4-Clause
# SPDX-FileCopyrightText: 2026 C2BTOR contributors

"""Expand certified independent array samples using original backend inputs.

Each group replaces a branch-free counted loop with one input per array root.
Collect those inputs across model frames, then emit calls in iteration/source
effect order. Array contents are never inferred from a later, modified state.
"""
from .cex_parser import ArrayValue


class SummaryRecovery:
    def __init__(self, mapping, model, trace, max_events=100000):
        self.model, self.trace = model, trace
        self.max_events, self.emitted = max_events, 0
        self.groups, self.pending = {}, {}
        report = mapping.get("array_loop_summary", {})
        count = report.get("nondet_initialization_loops", 0)
        if not count:
            return
        if report.get("expansion_format") != "independent-array-input-1":
            raise ValueError("nondet initialization summary has no supported expansion certificate")
        groups = report.get("nondet_summaries", [])
        if len(groups) != count:
            raise ValueError("incomplete nondet initialization summary certificates")
        for group in groups:
            identity = group["id"]
            calls = group["calls"]
            iterations, initial = int(group["iterations"]), int(group["counter_initial"])
            if identity in self.groups or iterations <= 0 or not calls:
                raise ValueError("invalid nondet initialization group")
            if sorted(call["event_order"] for call in calls) != list(range(len(calls))):
                raise ValueError("summary source-call order is incomplete or duplicated")
            calls = sorted(calls, key=lambda call: call["event_order"])
            members = {call["array_symbol"] for call in calls}
            bindings = {}
            for event in mapping.get("instructions", []):
                binding = event.get("nondet_summary", {})
                if binding.get("group_id") != identity:
                    continue
                symbol, node = binding["array_symbol"], binding["input_node"]
                if symbol in bindings:
                    raise ValueError("duplicate array binding in a nondet summary")
                declaration = model.by_node.get(node)
                if declaration is None or declaration.kind != "input" or declaration.sort.kind != "array":
                    raise ValueError("nondet summary input was removed or is not a native array input")
                bindings[symbol] = node
            if set(bindings) != members:
                raise ValueError("summary input bindings do not cover all original source calls")
            for call in calls:
                declaration = model.by_node[bindings[call["array_symbol"]]]
                if (not call["nondet_function"].startswith("__VERIFIER_nondet_") or
                        call["result_type"] not in {"signedbv", "unsignedbv"} or
                        call["result_width"] != declaration.sort.width):
                    raise ValueError("unsupported source return or storage width in nondet summary")
                first = initial * int(call["index_coefficient"]) + int(call["index_constant"])
                last = ((initial + iterations - 1) * int(call["index_coefficient"]) +
                        int(call["index_constant"]))
                if min(first, last) < 0 or max(first, last) >= 1 << declaration.sort.index_width:
                    raise ValueError("nondet summary indexes exceed original input sort")
            self.groups[identity] = dict(initial=initial, iterations=iterations,
                                         calls=calls, bindings=bindings,
                                         loop=group.get("loop_condition_entry"))

    def consume(self, event, time):
        return list(self.iter_consume(event, time))

    def iter_consume(self, event, time):
        """Yield certified samples without retaining an expanded loop in RAM."""
        binding = event.get("nondet_summary")
        if not binding:
            return
        identity, symbol = binding["group_id"], binding["array_symbol"]
        if identity not in self.groups:
            raise ValueError("executed array summary lacks an expansion certificate")
        group = self.groups[identity]
        node = group["bindings"].get(symbol)
        if node is None or node != binding["input_node"]:
            raise ValueError("executed summary array binding differs from its certificate")
        values = self.pending.setdefault(identity, {})
        if symbol in values:
            raise ValueError("summary group reentered before all array inputs were collected")
        value = self.trace.frames.get(time, {}).get("inputs", {}).get(node)
        if not isinstance(value, ArrayValue):
            raise ValueError(f"missing original backend array input for summary at frame {time}")
        values[symbol] = (time, value)
        if set(values) != set(group["bindings"]):
            return
        size = group["iterations"] * len(group["calls"])
        if self.emitted + size > self.max_events:
            raise ValueError("summary expansion exceeds source-event budget; no witness emitted")
        for iteration in range(group["iterations"]):
            counter = group["initial"] + iteration
            for call in group["calls"]:
                symbol = call["array_symbol"]
                input_frame, array = values[symbol]
                input_node = group["bindings"][symbol]
                sort = self.model.by_node[input_node].sort
                index = counter * int(call["index_coefficient"]) + int(call["index_constant"])
                bits = array.entries.get(format(index, f"0{sort.index_width}b"), array.default)
                if bits is None:
                    raise ValueError("summary source sample has no explicit backend array cell or default")
                if len(bits) != call["result_width"] or set(bits) - {"0", "1"}:
                    raise ValueError("summary source sample is non-concrete or has the wrong width")
                yield dict(call, value_bits=bits, summary_group=identity,
                                      summary_iteration=iteration, array_index=str(index),
                                      backend_input_node=input_node, backend_input_frame=input_frame,
                                      loop_condition_entry=group["loop"],
                                      iteration_first=call["event_order"] == 0,
                                      group_last=(iteration == group["iterations"] - 1 and
                                                  call["event_order"] == len(group["calls"]) - 1))
        del self.pending[identity]
        self.emitted += size

    def finish(self):
        if self.pending:
            raise ValueError("counterexample ended inside an incomplete array summary group")
