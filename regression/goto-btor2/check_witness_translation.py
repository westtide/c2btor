#!/usr/bin/env python3
"""End-to-end witness regressions; every run uses a fresh artifact directory."""

import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[2]
TOOL = ROOT / "scripts/c2btor_witness.py"
sys.path.insert(0, str(ROOT / "scripts"))
from c2btor_solver import ric3_command
CASES = {
    "branch": ("""extern int __VERIFIER_nondet_int(void);
extern void __VERIFIER_error(void);
int main(void) {
  int x = __VERIFIER_nondet_int();
  if (x == 7)
    __VERIFIER_error();
  return 0;
}
""", [7]),
    "repeat": ("""extern int __VERIFIER_nondet_int(void);
extern void __VERIFIER_error(void);
int main(void) {
  for (int i = 0; i < 2; ++i) {
    int x = __VERIFIER_nondet_int();
    if (x != -3) return 0;
  }
  __VERIFIER_error();
}
""", [-3, -3]),
    "multiple_bad": ("""extern int __VERIFIER_nondet_int(void);
extern void __VERIFIER_error(void);
int main(void) {
  int x = __VERIFIER_nondet_int();
  if (x == 1 && x == 2)
    __VERIFIER_error();
  if (x == 7)
    __VERIFIER_error();
  return 0;
}
""", [7]),
    "initial_bad": ("""extern void __VERIFIER_error(void);
int main(void) {
  __VERIFIER_error();
}
""", []),
    "same_line": ("""extern int __VERIFIER_nondet_int(void);
extern void __VERIFIER_error(void);
int f(void) {
  int x = __VERIFIER_nondet_int(), y = __VERIFIER_nondet_int();
  return x == -3 && y == 7;
}
int main(void) {
  if (f() && f()) __VERIFIER_error();
}
""", [-3, 7, -3, 7]),
    "wrapped_target": ("""extern void abort(void);
void reach_error(void) { abort(); }
void check(int condition) {
  if (!condition) reach_error();
}
int main(void) { check(0); }
""", []),
    "heap_linked": ((ROOT / "regression/goto-btor2/heap_linked_witness.c").read_text(), [7]),
    "malloc_model": ("""extern void *malloc(__SIZE_TYPE__);
extern void __VERIFIER_error(void);
int main(void) {
  int *p = malloc(sizeof(int));
  if (!p) return 0;
  *p = 7;
  if (*p == 7) __VERIFIER_error();
}
""", []),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("cbmc", "ric3", "btorsim"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--engine", choices=["bmc", "wl-bmc"], default="bmc")
    parser.add_argument("--cbmc-arg", action="append", default=[])
    parser.add_argument("--btormc", type=Path, help="optional backend for heap-model regression")
    parser.add_argument("--cpachecker", type=Path)
    parser.add_argument("--solver")
    parser.add_argument("--integer-encoding", action="store_true")
    parser.add_argument("--no-floats", action="store_true")
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    if args.output_dir:
        args.output_dir.mkdir(parents=True, exist_ok=False)
        directory = args.output_dir.resolve()
    else:
        directory = Path(tempfile.mkdtemp(prefix="c2btor-witness-regression-")).resolve()
    print(directory, flush=True)
    report = []

    def call(command, name, success=True):
        result = subprocess.run([str(x) for x in command], capture_output=True,
                                text=True, timeout=65, cwd=ROOT)
        (directory / (name + ".log")).write_text(result.stdout + result.stderr)
        assert (result.returncode == 0) == success, (name, result.returncode, result.stdout, result.stderr)
        report.append({"test": name, "passed": True})
        return result.stdout

    def translate(model_dir, witness, name, success=True):
        target = directory / name
        call([sys.executable, TOOL, "translate", "--model", model_dir / "model.btor2",
              "--map", model_dir / "model.map.json", "--witness", witness,
              "--btorsim", args.btorsim, "--output-dir", target], name, success)
        if not success:
            assert not (target / "witness.yml").exists()
        return target / "witness.yml"

    def validate(witness, name, success=True):
        command = [sys.executable, TOOL, "validate", "--witness", witness,
                   "--cpachecker", args.cpachecker, "--output-dir", directory / name,
                   "--timeout", "35"]
        if args.solver:
            command += ["--solver", args.solver]
        if args.integer_encoding:
            command += ["--integer-encoding"]
        if args.no_floats:
            command += ["--no-floats"]
        call(command, name, success)
        result = json.loads((directory / name / "result.json").read_text())
        assert (result["status"] == "confirmed") == success

    for name, (code, expected_values) in CASES.items():
        program = directory / (name + ".c")
        program.write_text(code)
        model_dir = directory / (name + "-export")
        flags = ["--", *args.cbmc_arg, *(["--32"] if name == "repeat" else [])]
        specification = []
        if name == "wrapped_target":
            prop = directory / "reach_error.prp"
            prop.write_text("CHECK( init(main()), LTL(G ! call(reach_error())) )\n")
            specification = ["--spec", prop]
        call([sys.executable, TOOL, "export", "--cbmc", args.cbmc,
              "--program", program, "--output-dir", model_dir,
              *specification, *flags], name + "-export")
        mapping = json.loads((model_dir / "model.map.json").read_text())
        assert all(entry["first_node"] <= entry["pc_guard_node"] <= entry["last_node"]
                   for entry in mapping["instructions"])
        backend = directory / (name + ".witness")
        solver = ric3_command(args.ric3, model_dir / "model.btor2", args.engine, 60, 400)
        if name in {"malloc_model", "heap_linked"} and args.btormc:
            solver = [args.btormc, "--bound-max=400", "--trace-gen-full", model_dir / "model.btor2"]
        backend.write_text(call(solver, name + "-solver"))
        witness_path = translate(model_dir, backend, name + "-translate")
        witness = json.loads(witness_path.read_text())[0]
        points = [s["segment"][0]["waypoint"] for s in witness["content"]]
        actual = [int(w["constraint"]["value"].split("==")[1]) for w in points[:-1]]
        assert actual == expected_values, (name, actual)
        assert all(w["type"] == "function_return" for w in points[:-1])
        assert points[-1]["type"] == "target"
        assert witness["metadata"]["format_version"] == "2.0"
        assert witness["metadata"]["task"]["data_model"] == ("ILP32" if name == "repeat" else "LP64")
        if name == "multiple_bad":
            assert "b1\n" in backend.read_text()
            assert points[-1]["location"]["line"] == 8
        if name == "wrapped_target":
            assert points[-1]["location"]["line"] == 4
        if name == "same_line":
            columns = [w["location"]["column"] for w in points[:-1]]
            assert columns[0] < columns[1] and columns[:2] == columns[2:]
        if name == "malloc_model":
            assert any("nondet_function" in i and i["source"]["file_name"].startswith("<")
                       for i in mapping["instructions"])
        if args.cpachecker:
            validate(witness_path, name + "-validate")
        if name != "branch":
            continue

        # Missing internal state frames are completed by the simulator.
        sparse = []
        state_section = False
        for line in backend.read_text().splitlines():
            if line.startswith("#"):
                state_section = True
                if line == "#0":
                    sparse.append(line)
            elif line.startswith("@") or line == ".":
                state_section = False
                sparse.append(line)
            elif not state_section:
                sparse.append(line)
        sparse_path = directory / "sparse.witness"
        sparse_path.write_text("\n".join(sparse) + "\n")
        translate(model_dir, sparse_path, "sparse-translate")

        wrong_backend = directory / "wrong-backend.witness"
        wrong_backend.write_text(sparse_path.read_text().replace("00000000000000000000000000000111", "00000000000000000000000000001000"))
        translate(model_dir, wrong_backend, "wrong-backend-rejected", False)
        truncated = directory / "truncated.witness"
        truncated.write_text(sparse_path.read_text().replace(".\n", ""))
        translate(model_dir, truncated, "truncated-rejected", False)
        safe = directory / "safe.witness"
        safe.write_text("UNSAT\n")
        translate(model_dir, safe, "unsat-rejected", False)
        original = (model_dir / "model.btor2").read_text()
        (model_dir / "model.btor2").write_text(original + "; changed\n")
        translate(model_dir, backend, "model-mismatch-rejected", False)
        (model_dir / "model.btor2").write_text(original)
        program.write_text(code + "/* changed */\n")
        translate(model_dir, backend, "source-mismatch-rejected", False)
        program.write_text(code)
        if args.cpachecker:
            points[0]["constraint"]["value"] = points[0]["constraint"]["value"].replace("7", "8")
            wrong_yaml = directory / "wrong-constraint.yml"
            wrong_yaml.write_text(json.dumps([witness]))
            validate(wrong_yaml, "wrong-constraint-rejected", False)

    # Real SAFE result, not only a parser fixture.
    program = directory / "safe.c"
    program.write_text("extern void __VERIFIER_error(void);\nint main(void) { if (0) __VERIFIER_error(); return 0; }\n")
    model_dir = directory / "safe-export"
    call([sys.executable, TOOL, "export", "--cbmc", args.cbmc, "--program", program,
          "--output-dir", model_dir], "safe-export")
    backend = directory / "safe-real.witness"
    backend.write_text(call(ric3_command(args.ric3, model_dir / "model.btor2", "ic3", 30), "safe-solver"))
    translate(model_dir, backend, "safe-real-rejected", False)

    # Standard BTOR2 state/input sections with the same time form one frame.
    spec = importlib.util.spec_from_file_location("witness", TOOL)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    frames = module.read_frames("#0\n0 01 pc#0\n@0\n0 11 input@0\n#1\n0 10 pc#1\n@1\n.\n")
    assert len(frames) == 2 and frames[0]["inputs"][0] == "11"
    save = directory / "results.json"
    save.write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS: {len(report)} checks; {save}")


if __name__ == "__main__":
    main()
