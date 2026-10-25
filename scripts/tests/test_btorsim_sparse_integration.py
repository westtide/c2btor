"""Opt-in semantic regressions for sparse known-default BtorSim arrays.

Set BTORSIM_BIN to the simulator under test. No solver or source translator is
needed. Complete tiny models, witnesses, commands and outputs remain in the
printed temporary directory, including when a test fails.
"""

import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest


BTORSIM = os.environ.get("BTORSIM_BIN")


@unittest.skipUnless(BTORSIM, "set BTORSIM_BIN to run sparse-array integration checks")
class BtorSimSparseIntegration(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(tempfile.mkdtemp(prefix="btorsim-sparse-regression-"))
        print(f"\nSparse-array integration evidence: {cls.root}", flush=True)

    def command(self, name, *arguments):
        command = [str(BTORSIM), *map(str, arguments)]
        (self.root / (name + ".command.json")).write_text(json.dumps(command, indent=2) + "\n")
        result = subprocess.run(command, capture_output=True, text=True, timeout=20)
        (self.root / (name + ".stdout")).write_text(result.stdout)
        (self.root / (name + ".stderr")).write_text(result.stderr)
        return result

    def check_bad(self, name, model, witness, depth=0, accepted=True):
        result = self.command(name, "-c", "-v", model, witness)
        output = result.stdout + result.stderr
        if accepted:
            self.assertEqual(result.returncode, 0, output)
            self.assertRegex(output, rf"reached bad state properties.*\bb0@{depth}\b")
        else:
            self.assertNotEqual(result.returncode, 0, output)
            self.assertNotRegex(output, rf"reached bad state properties.*\bb0@{depth}\b")

    def check_row_order(self, kind):
        for width in (2, 80):
            # A high bit beyond uint64_t distinguishes wide-index handling
            # from accidental machine-integer truncation.
            index = 0 if width == 2 else (1 << 79)
            bits = format(index, f"0{width}b")
            other = format(index + 1, f"0{width}b")
            model = self.root / f"{kind}-{width}.btor2"
            model.write_text(f"""1 sort bitvec 1
2 sort bitvec {width}
3 sort bitvec 8
4 sort array 2 3
5 const 2 {bits}
6 const 2 {other}
7 zero 3
8 one 3
9 {kind} 4 memory
10 read 3 9 5
11 read 3 9 6
12 eq 1 10 7
13 eq 1 11 8
14 and 1 12 13
15 bad 14
""")
            for default_first in (False, True):
                for accepted in (True, False):
                    name = f"{kind}-{width}-default-first-{default_first}-accept-{accepted}"
                    with self.subTest(kind=kind, width=width, default_first=default_first,
                                      accepted=accepted):
                        indexed = f"0 [{bits}] {'00000000' if accepted else '00000001'}"
                        default = "0 [*] 00000001"
                        rows = [default, indexed] if default_first else [indexed, default]
                        assignments = "\n".join(rows) + "\n"
                        body = "#0\n@0\n" + assignments if kind == "input" else "#0\n" + assignments + "@0\n"
                        witness = self.root / (name + ".cexb")
                        witness.write_text("sat\nb0\n" + body + ".\n")
                        self.check_bad(name, model, witness, accepted=accepted)

    def test_input_indexed_zero_and_default_one_in_either_order(self):
        self.check_row_order("input")

    def test_state_indexed_zero_and_default_one_in_either_order(self):
        self.check_row_order("state")

    def test_vcd_emits_nondefault_write_and_reset_to_default(self):
        for width in (2, 80):
            for initialization in ("implicit-zero", "explicit-zero", "explicit-42"):
                name = f"reset-{width}-{initialization}"
                with self.subTest(width=width, initialization=initialization):
                    fallback = 42 if initialization == "explicit-42" else 0
                    override = 7 if fallback else 1
                    index = 0 if width == 2 else (1 << 79) + 1
                    bits = format(index, f"0{width}b")
                    init = "" if initialization == "implicit-zero" else "14 init 4 12 10\n"
                    model = self.root / (name + ".btor2")
                    model.write_text(f"""1 sort bitvec 1
2 sort bitvec {width}
3 sort bitvec 8
4 sort array 2 3
5 sort bitvec 2
6 const 2 {bits}
7 zero 5
8 one 5
9 constd 5 2
10 constd 3 {fallback}
11 constd 3 {override}
12 state 4 memory
13 state 5 pc
{init}15 init 5 13 7
16 eq 1 13 7
17 ite 3 16 11 10
18 write 4 12 6 17
19 next 4 12 18
20 add 5 13 8
21 next 5 13 20
22 eq 1 13 9
23 read 3 12 6
24 eq 1 23 10
25 and 1 22 24
26 bad 25
""")
                    witness = self.root / (name + ".cexb")
                    # Explicitly observe the initially default-valued cell.
                    # It must remain observable when a BTOR2 write resets it.
                    witness.write_text(f"sat\nb0\n#0\n0 [{bits}] {fallback:08b}\n"
                                       "@0\n#1\n@1\n#2\n@2\n.\n")
                    self.check_bad(name + "-check", model, witness, depth=2)
                    vcd = self.root / (name + ".vcd")
                    result = self.command(name + "-vcd", "--states", "--vcd", vcd, model, witness)
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    text = vcd.read_text()
                    identifiers = re.findall(r"^\$var\s+\S+\s+8\s+(\S+)\s+memory<([^>]+)>\s+\$end$",
                                             text, re.M)
                    self.assertEqual(len(identifiers), 1, text)
                    identifier, index_hex = identifiers[0]
                    self.assertEqual(int(index_hex, 16), index)
                    changes = {}
                    timestamp = None
                    for line in text.split("$enddefinitions $end", 1)[1].splitlines():
                        if line.startswith("#"):
                            timestamp = int(line[1:])
                        match = re.fullmatch(r"b([01]+)\s+(\S+)", line)
                        if match and match[2] == identifier:
                            changes[timestamp] = int(match[1], 2)
                    self.assertEqual([changes.get(time) for time in (0, 10, 20)],
                                     [fallback, override, fallback], text)


if __name__ == "__main__":
    unittest.main()
