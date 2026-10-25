from copy import deepcopy
from types import SimpleNamespace
import unittest

from scripts.btor2_parser import Declaration, Sort
from scripts.cex_parser import ArrayValue, Trace
from scripts.summary_recovery import SummaryRecovery


class SummaryRecoveryTests(unittest.TestCase):
    def fixtures(self, roots=("a", "b")):
        nodes = {i + 10: Declaration(i + 10, i, "input", Sort("array", 8, 4), root)
                 for i, root in enumerate(roots)}
        calls = [{"array_symbol": root, "event_order": i, "index_coefficient": "1",
                  "index_constant": "0", "nondet_function": "__VERIFIER_nondet_int",
                  "result_type": "signedbv", "result_width": 8, "source": {"line": 4 + i}}
                 for i, root in enumerate(roots)]
        events = [{"nondet_summary": {"group_id": "g", "array_symbol": root, "input_node": i + 10}}
                  for i, root in enumerate(roots)]
        mapping = {"instructions": events, "array_loop_summary": {
            "nondet_initialization_loops": 1, "expansion_format": "independent-array-input-1",
            "nondet_summaries": [{"id": "g", "counter_initial": "0", "iterations": "2", "calls": calls}]}}
        trace = Trace([0], {i: {"inputs": {i + 10: ArrayValue("00000000", {
            "0000": format(i + 1, "08b"), "0001": format(i + 3, "08b")})}}
                           for i in range(len(roots))})
        return mapping, SimpleNamespace(by_node=nodes), trace

    def test_cross_frame_arrays_restore_iteration_order(self):
        mapping, model, trace = self.fixtures()
        recovery = SummaryRecovery(mapping, model, trace)
        self.assertEqual(recovery.consume(mapping["instructions"][0], 0), [])
        calls = recovery.consume(mapping["instructions"][1], 1)
        self.assertEqual([int(c["value_bits"], 2) for c in calls], [1, 2, 3, 4])
        self.assertEqual([c["backend_input_frame"] for c in calls], [0, 1, 0, 1])
        self.assertEqual([c["summary_iteration"] for c in calls], [0, 0, 1, 1])
        recovery.finish()

    def test_tiled_indexes_and_nonzero_counter(self):
        mapping, model, trace = self.fixtures(("a",))
        group = mapping["array_loop_summary"]["nondet_summaries"][0]
        group["counter_initial"] = "3"
        first = group["calls"][0]
        first.update(index_coefficient="2", index_constant="-6")
        second = dict(first, event_order=1, index_constant="-5")
        group["calls"].append(second)
        trace.frames[0]["inputs"][10] = ArrayValue(None, {
            format(i, "04b"): format(i + 7, "08b") for i in range(4)})
        recovery = SummaryRecovery(mapping, model, trace)
        calls = recovery.consume(mapping["instructions"][0], 0)
        self.assertEqual([c["array_index"] for c in calls], ["0", "1", "2", "3"])
        self.assertEqual([int(c["value_bits"], 2) for c in calls], [7, 8, 9, 10])

    def test_explicit_zero_default_is_original_evidence(self):
        mapping, model, trace = self.fixtures(("a",))
        trace.frames[0]["inputs"][10] = ArrayValue("00000000")
        calls = SummaryRecovery(mapping, model, trace).consume(mapping["instructions"][0], 0)
        self.assertEqual([c["value_bits"] for c in calls], ["00000000", "00000000"])

    def test_no_missing_array_or_cell_is_guessed(self):
        mapping, model, trace = self.fixtures(("a",))
        for value in (None, ArrayValue(None, {"0000": "00000001"})):
            with self.subTest(value=value), self.assertRaises(ValueError):
                trace.frames[0]["inputs"][10] = value
                SummaryRecovery(mapping, model, trace).consume(mapping["instructions"][0], 0)

    def test_missing_binding_or_duplicate_order_is_rejected(self):
        mapping, model, trace = self.fixtures()
        altered = deepcopy(mapping)
        altered["instructions"].pop()
        with self.assertRaisesRegex(ValueError, "bindings"):
            SummaryRecovery(altered, model, trace)
        altered = deepcopy(mapping)
        altered["array_loop_summary"]["nondet_summaries"][0]["calls"][1]["event_order"] = 0
        with self.assertRaisesRegex(ValueError, "order"):
            SummaryRecovery(altered, model, trace)

    def test_incomplete_group_or_reentry_fails(self):
        mapping, model, trace = self.fixtures()
        recovery = SummaryRecovery(mapping, model, trace)
        recovery.consume(mapping["instructions"][0], 0)
        with self.assertRaisesRegex(ValueError, "incomplete"):
            recovery.finish()
        with self.assertRaisesRegex(ValueError, "reentered"):
            recovery.consume(mapping["instructions"][0], 0)

    def test_event_budget_fails_without_truncation(self):
        mapping, model, trace = self.fixtures(("a",))
        with self.assertRaisesRegex(ValueError, "budget"):
            SummaryRecovery(mapping, model, trace, max_events=1).consume(mapping["instructions"][0], 0)

    def test_original_legacy_map_requires_reexport(self):
        mapping, model, trace = self.fixtures()
        del mapping["array_loop_summary"]["expansion_format"]
        with self.assertRaisesRegex(ValueError, "certificate"):
            SummaryRecovery(mapping, model, trace)

    def test_finished_group_can_execute_again_with_fresh_inputs(self):
        mapping, model, trace = self.fixtures(("a",))
        trace.frames[1] = {"inputs": {10: ArrayValue("11111111")}}
        recovery = SummaryRecovery(mapping, model, trace)
        first = recovery.consume(mapping["instructions"][0], 0)
        second = recovery.consume(mapping["instructions"][0], 1)
        self.assertEqual(first[0]["value_bits"], "00000001")
        self.assertEqual(second[0]["value_bits"], "11111111")
        recovery.finish()


if __name__ == "__main__":
    unittest.main()
