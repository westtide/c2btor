# SPDX-License-Identifier: BSD-4-Clause
# SPDX-FileCopyrightText: 2026 C2BTOR contributors
"""Runtime packager must reject invalid inputs before building dependencies."""
from pathlib import Path
import platform
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]


@unittest.skipUnless(platform.system() == "Linux" and platform.machine() == "x86_64",
                     "runtime packager targets Linux x86_64")
class RuntimePackagerPreflightTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / "scripts").mkdir()
        self.script = self.root / "scripts/build_svcomp.sh"
        shutil.copyfile(ROOT / "scripts/build_svcomp.sh", self.script)

    def run_packager(self, *args):
        return subprocess.run(["bash", str(self.script), *map(str, args)],
                              capture_output=True, text=True, timeout=10)

    def prepare_notices_and_setup(self):
        (self.root / "LICENSES").mkdir()
        for name in ("LICENSES/CBMC-BSD-4-Clause.txt",
                     "LICENSES/C2BTOR-BSD-4-Clause.txt"):
            (self.root / name).write_text("test fixture", encoding="utf-8")
        carat = self.root / "checkers/carat"
        carat.mkdir(parents=True)
        (carat / "setup.sh").write_text("exit 99\n", encoding="utf-8")

    def test_usage_without_output_directory(self):
        result = self.run_packager()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("usage:", result.stderr)

    def test_missing_notice_fails_before_dependency_setup(self):
        (self.root / "LICENSES").mkdir()
        (self.root / "LICENSES/CBMC-BSD-4-Clause.txt").write_text(
            "test fixture", encoding="utf-8")
        output = self.root / "output"
        result = self.run_packager(output)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("missing project notice: LICENSES/C2BTOR-BSD-4-Clause.txt",
                      result.stderr)
        self.assertFalse(output.exists())

    def test_existing_output_is_preserved(self):
        self.prepare_notices_and_setup()
        output = self.root / "output"
        output.mkdir()
        sentinel = output / "sentinel"
        sentinel.write_text("keep", encoding="utf-8")
        result = self.run_packager(output)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("output already exists", result.stderr)
        self.assertEqual(sentinel.read_text(encoding="utf-8"), "keep")


if __name__ == "__main__":
    unittest.main()
