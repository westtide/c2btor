# SPDX-License-Identifier: BSD-4-Clause
"""Public converter contracts; set C2BTOR_BINARY to exercise the executable."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from scripts.btor2_parser import Btor2Model


ROOT = Path(__file__).resolve().parents[2]
BINARY = os.environ.get("C2BTOR_BINARY")


@unittest.skipUnless(BINARY, "set C2BTOR_BINARY to test the converter")
class ConverterCliTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.source = self.directory / "program.c"
        self.source.write_text('int main(void) { __CPROVER_assert(1, "p"); }\n')
        self.model = self.directory / "model.btor2"

    def run_converter(self, *options, sources=None):
        return subprocess.run(
            [str(Path(BINARY).resolve()), *(str(p) for p in (sources or [self.source])),
             "--goto-btor2", "--goto-btor2-out", str(self.model), *options],
            capture_output=True, text=True, timeout=30, cwd=self.directory)

    def test_contradictory_flags_fail_before_touching_output(self):
        for positive, negative in (
            ("32", "64"), ("inline", "no-inline"),
            ("goto-btor2-lbe", "goto-btor2-no-lbe"),
            ("goto-btor2-scalar-blocks", "goto-btor2-no-scalar-blocks"),
            ("goto-btor2-slice-property", "goto-btor2-no-slice-property"),
            ("goto-btor2-merge-bads", "goto-btor2-no-merge-bads"),
            ("goto-btor2-optimize-state", "goto-btor2-no-optimize-state"),
        ):
            with self.subTest(positive=positive):
                self.model.write_text("sentinel")
                result = self.run_converter("--" + positive, "--" + negative)
                self.assertEqual(result.returncode, 1, result.stderr)
                self.assertIn("conflicts", result.stderr)
                self.assertEqual(self.model.read_text(), "sentinel")

    def test_retired_demo_options_are_rejected(self):
        for options in (["--btor2-demo"], ["--btor2-out", str(self.model)]):
            with self.subTest(options=options):
                result = subprocess.run(
                    [str(Path(BINARY).resolve()), str(self.source), *options],
                    capture_output=True, text=True, timeout=10)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("Unknown option", result.stderr)
                self.assertFalse(self.model.exists())

    def test_repeated_representation_values_must_agree(self):
        for option, first, second in (("array", "bv", "array"), ("memory", "object", "global")):
            with self.subTest(option=option):
                result = self.run_converter("--" + option, first, "--" + option, second)
                self.assertEqual(result.returncode, 1, result.stderr)
                self.assertIn("conflicting repeated values", result.stderr)
                self.assertFalse(self.model.exists())

    def test_model_map_aliases_do_not_truncate_existing_data(self):
        aliases = [self.model, self.directory / "sub" / ".." / self.model.name]
        (self.directory / "sub").mkdir()
        hardlink = self.directory / "hardlink"
        symlink = self.directory / "symlink"
        self.model.write_text("sentinel")
        os.link(self.model, hardlink)
        symlink.symlink_to(self.model)
        for alias in [*aliases, hardlink, symlink]:
            with self.subTest(alias=alias):
                result = self.run_converter("--goto-btor2-map-out", str(alias))
                self.assertEqual(result.returncode, 1, result.stderr)
                self.assertIn("distinct paths", result.stderr)
                self.assertEqual(self.model.read_text(), "sentinel")

    def test_default_modes_only_enable_applicable_stages(self):
        for memory, array in (("object", "bv"), ("object", "array"), ("object", "mixed"),
                              ("global", "bv"), ("global", "array")):
            for no_lbe in ([], ["--goto-btor2-no-lbe"]):
                with self.subTest(memory=memory, array=array, no_lbe=no_lbe):
                    result = self.run_converter("--memory", memory, "--array", array, *no_lbe)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    Btor2Model(self.model)

    def test_bv_prunes_unreachable_capacity_without_array_storage(self):
        result = self.run_converter("--array", "bv",
                                   sources=[ROOT / "test/c2btor_optimizations/unused_capacity.c"])
        self.assertEqual(result.returncode, 0, result.stderr)
        Btor2Model(self.model)
        self.assertNotRegex(self.model.read_text(), r"(?m)^\d+ sort array ")
        result = self.run_converter("--array", "bv", "--goto-btor2-no-optimize-state",
                                   sources=[ROOT / "test/c2btor_optimizations/unused_capacity.c"])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("exceeds representable width", result.stderr)

    def test_upstream_frontend_regressions_typecheck(self):
        fixtures = ROOT / "test/frontend"
        for names in (
            ["qualified_auto_type.c"], ["compound_literal_static_init.c"],
            ["named_address_space.c"], ["incomplete_array_def.c", "incomplete_array_ref.c"],
        ):
            for architecture in ("--32", "--64"):
                with self.subTest(names=names, architecture=architecture):
                    # Exercise the upstream frontend independently of BTOR2's
                    # supported expression subset and source-property selection.
                    result = subprocess.run(
                        [str(Path(BINARY).resolve()), architecture, "--show-symbol-table",
                         *(str(fixtures / name) for name in names)],
                        capture_output=True, text=True, timeout=30, cwd=self.directory)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertIn("main", result.stdout)


if __name__ == "__main__":
    unittest.main()
