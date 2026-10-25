import json
from pathlib import Path
import tempfile
import unittest

from scripts.btor2_parser import Btor2Model
from scripts.cex_parser import ArrayValue, open_cex, parse_cex
from scripts.source_map import digest, enrich_map, load_map


class ParserTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.source = self.root / "test.c"
        self.source.write_text("int main(void) { return 0; }\n")
        self.path = self.root / "model.btor2"
        self.path.write_text("1 sort bitvec 1\n3 sort bitvec 8\n5 sort bitvec 64\n"
                             "7 sort array 5 3\n10 state 3 pc\n12 input 3 nondet\n"
                             "15 state 7 memory\n18 input 7 array_input\n"
                             "20 zero 3\n22 init 3 10 20\n23 next 3 10 12\n"
                             "25 eq 1 10 12\n30 bad 25\n")
        self.model = Btor2Model(self.path)
        self.trace = ("sat\nb0\n#0\n0 00000000 pc\n"
                      "1 [*] 11111111 memory\n1 [" + "0" * 64 + "] 00000111\n"
                      "@0\n0 11111101 nondet\n1 [*] 00000000 array_input\n"
                      "@1\n0 00000111\n1 [*] 00000000\n.\n")

    def test_ordinals_are_not_node_ids(self):
        trace = parse_cex(self.trace, self.model)
        self.assertEqual(trace.frames[0]["inputs"][12], "11111101")
        self.assertEqual(trace.frames[1]["inputs"][12], "00000111")
        self.assertIsInstance(trace.frames[0]["states"][15], ArrayValue)
        self.assertEqual(self.model.states[1].node, 15)
        self.assertEqual(self.model.inputs[1].node, 18)

    def test_wide_sparse_array(self):
        array = parse_cex(self.trace, self.model).frames[0]["states"][15]
        self.assertEqual(array.default, "11111111")
        self.assertEqual(array.entries, {"0" * 64: "00000111"})

    def test_reject_corrupt_trace(self):
        variants = [self.trace.replace("b0", "b1"),
                    self.trace.replace("@1", "@2"),
                    self.trace.replace("0 11111101", "0 1111110x"),
                    self.trace.replace("0 11111101", "12 11111101"),
                    self.trace.replace(".\n", ""),
                    self.trace.replace("@1", "@0"),
                    self.trace.replace("0 11111101", "0 1"),
                    self.trace.replace("1 [*] 11111111", "1 [*] 11111111\n1 [*] 00000000")]
        for text in variants:
            with self.subTest(text=text), self.assertRaises(ValueError):
                parse_cex(text, self.model)

    def test_no_safe_or_unknown_trace(self):
        for text in ("unsat\n", "unknown\n", "unsat\n" + self.trace):
            with self.assertRaises(ValueError):
                parse_cex(text, self.model)

    def test_streaming_frames_match_compatibility_parser_and_reject_trailing_data(self):
        path = self.root / 'trace.cexb'
        path.write_text(self.trace)
        with open_cex(path, self.model) as reader:
            self.assertEqual(dict(reader), parse_cex(self.trace, self.model).frames)
            self.assertEqual(reader.frame_count, 2)
            self.assertTrue(reader.complete)
            self.assertEqual(reader.bads, [0])
        for text in ("Carat log\n" + self.trace, self.trace + "trailing log\n", self.trace.replace('@1', '@0'),
                     self.trace.replace('#0', '@0'), self.trace.replace('.\n', '')):
            path.write_text(text)
            with self.assertRaises(ValueError), open_cex(path, self.model) as reader:
                for _ in reader:
                    pass

    def test_streaming_context_validates_an_unconsumed_tail(self):
        path = self.root / 'trace.cexb'
        path.write_text(self.trace.replace('0 00000111', '0 00x00111'))
        with self.assertRaisesRegex(ValueError, 'scalar'), open_cex(path, self.model) as reader:
            next(reader)

    def test_streaming_retains_no_frame_history(self):
        import tracemalloc
        path = self.root / 'many.cexb'
        with path.open('w') as stream:
            stream.write('sat\nb0\n#0\n')
            for i in range(20000):
                stream.write(f'@{i}\n0 00000111\n')
            stream.write('.\n')
        tracemalloc.start()
        try:
            with open_cex(path, self.model) as reader:
                for time, frame in reader:
                    self.assertEqual(frame['inputs'][12], '00000111')
                self.assertEqual(time, 19999)
                self.assertEqual(reader.frame_count, 20000)
            self.assertLess(tracemalloc.get_traced_memory()[1], 4 * 1024 ** 2)
        finally:
            tracemalloc.stop()

    def mapping(self):
        return {"format_version": "2", "pc_node": 10, "int_width": 32,
                "long_width": 32, "pointer_width": 32,
                "input_files": [str(self.source)], "source_hashes": {str(self.source): digest(self.source)},
                "model_sha256": self.model.sha256, "states": [], "instructions": [],
                "specification": "CHECK( init(main()), LTL(G ! call(reach_error())) )"}

    def test_enriched_map_roundtrip(self):
        mapping = enrich_map(self.mapping(), self.path)
        path = self.root / "map.json"
        path.write_text(json.dumps(mapping))
        result, model = load_map(path, self.path, self.source, mapping["specification"], "ILP32")
        self.assertEqual(result["data_model"], "ILP32")
        self.assertEqual(model.sha256, self.model.sha256)
        with self.assertRaisesRegex(ValueError, "data model"):
            load_map(path, self.path, expected_data_model="LP64")
        with self.assertRaisesRegex(ValueError, "property"):
            load_map(path, self.path, specification="other")
        self.source.write_text("changed\n")
        with self.assertRaisesRegex(ValueError, "source hash"):
            load_map(path, self.path)

    def test_model_hash_binding(self):
        path = self.root / "map.json"
        path.write_text(json.dumps(self.mapping()))
        self.path.write_text(self.path.read_text() + "; changed\n")
        with self.assertRaisesRegex(ValueError, "model hash"):
            load_map(path, self.path)




if __name__ == "__main__":
    unittest.main()
