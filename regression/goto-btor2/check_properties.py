#!/usr/bin/env python3
"""Conversion/parser regression for property preservation and selection."""

import argparse
import json
from pathlib import Path
import subprocess
import tempfile


ERROR = 'void reach_error(void) { __CPROVER_assert(0, "error"); }\n'
CASES = {
    "folded": ERROR + "int main(void) { unsigned x=1; int y=-1; "
    "if(x > y) reach_error(); }\n",
    "unused": ERROR + "int main(void) { return 0; }\n",
    "multiple": ERROR + "extern int __VERIFIER_nondet_int(void);\n"
    "int main(void) { int x=__VERIFIER_nondet_int(); "
    "if(x==1 && x==2) reach_error(); if(x==7) reach_error(); }\n",
    "memory": ERROR + "int main(void) { int a[2]={0,1}; "
    "int *p=&a[1]; if(*p==1) reach_error(); }\n",
    "ordinary": ERROR + "extern int __VERIFIER_nondet_int(void);\n"
    "int main(void) { int x=__VERIFIER_nondet_int(); "
    "if(x==1) __CPROVER_assert(0, \"ordinary\"); "
    "if(x==2) reach_error(); }\n",
    "unsupported": ERROR + "extern void unknown(void); "
    "int main(void) { unknown(); }\n",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c2btor", "--cbmc", dest="cbmc", type=Path, required=True)
    parser.add_argument("--catbtor", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = args.output or Path(tempfile.mkdtemp(prefix="c2btor-properties-"))
    if args.output:
        root.mkdir(parents=True, exist_ok=False)
    root = root.resolve()
    report = []

    def call(command, directory, stage):
        command = [str(x) for x in command]
        (directory / (stage + ".command.json")).write_text(
            json.dumps(command, indent=2) + "\n")
        result = subprocess.run(command, capture_output=True, timeout=30)
        (directory / (stage + ".stdout")).write_bytes(result.stdout)
        (directory / (stage + ".stderr")).write_bytes(result.stderr)
        return result.returncode

    def convert(case, mode, memory="global", array="bv", failure=False):
        directory = root / f"{case}-{mode}-{memory}-{array}"
        directory.mkdir()
        source = directory / "input.c"
        source.write_text(CASES[case])
        model, mapping = directory / "model.btor2", directory / "model.map.json"
        flags = [] if mode == "default" else [
            "--goto-btor2-error-function", "typo" if mode == "typo" else "reach_error"]
        if mode in ("selected", "merged", "selected_no_heap"):
            flags += ["--goto-btor2-reach-only"]
        if mode == "merged":
            flags += ["--goto-btor2-merge-bads"]
        if mode in ("legacy", "legacy_no_heap"):
            flags += ["--goto-btor2-merge-properties"]
        no_heap = mode in ("legacy_no_heap", "selected_no_heap")
        if no_heap:
            flags += ["--goto-btor2-no-heap-guards"]
        rc = call([
            args.cbmc.resolve(), "--32", "--inline", "--goto-btor2",
            "--no-standard-checks", "--no-pointer-check", "--no-bounds-check",
            "--no-built-in-assertions", "--memory", memory, "--array", array,
            *flags, "--goto-btor2-out", model, "--goto-btor2-map-out", mapping,
            source], directory, "conversion")
        if failure:
            assert rc != 0 and (not model.exists() or not model.stat().st_size)
            report.append({"case": directory.name, "rejected": True})
            return
        assert rc == 0, directory
        assert call([args.catbtor.resolve(), model], directory, "parser") == 0
        nodes = {int(f[0]): f for line in model.read_text().splitlines()
                 if (f := line.split()) and f[0].isdigit()}
        bad = {nid for nid, f in nodes.items() if f[1] == "bad"}
        assert bad, directory
        data = json.loads(mapping.read_text())
        properties = data["source_properties"]
        if mode in ("selected", "merged", "selected_no_heap"):
            assert all(p["property_class"] == "unreach-call" for p in properties)
            assert {p["bad_node"] for p in properties} == bad
            for p in data["memory"]["properties"]:
                assert p["bad_node"] == 0 and nodes[p["output_node"]][1] == "output"
        if mode == "merged":
            assert len(bad) == 1
        if no_heap:
            assert data["property_selection"]["no_heap_guards"]
            assert not data["memory"]["properties"]
            assert {p["bad_node"] for p in properties} == bad
        if mode in ("legacy", "legacy_no_heap"):
            assert data["property_selection"]["merged"]
            assert len({p["bad_node"] for p in properties}) == 1
        if case in ("folded", "unused"):
            reason = ("unreachable_after_constant_folding" if case == "folded"
                      else "no_assertion_in_program" if mode == "default"
                      else "no_target_call_in_inlined_entry")
            assert any(p["elimination_reason"] == reason for p in properties)
            assert all(nodes[p["condition_node"]][1] == "zero" for p in properties)
        if case == "multiple":
            assert len(properties) == 2
            if mode == "selected":
                assert len(bad) == 2
            if mode == "merged":
                condition = int(nodes[next(iter(bad))][2])
                assert nodes[condition][1] == "or"
                assert set(map(int, nodes[condition][3:5])) == {
                    p["condition_node"] for p in properties}
        if case == "ordinary":
            assert len(properties) == (2 if mode == "target" else 1)
        for instruction in data["instructions"]:
            if instruction["bad_node"]:
                assert instruction["bad_node"] in bad
                assert instruction["bad_condition_node"] in nodes
        report.append({"case": directory.name, "bads": len(bad),
                       "source_properties": len(properties), "parser": "passed"})

    convert("folded", "default")
    for case in ("folded", "unused", "multiple", "ordinary"):
        for mode in ("target", "selected", "merged"):
            convert(case, mode)
    for memory in ("global", "object"):
        for array in ("array", "bv"):
            convert("memory", "merged", memory, array)
    convert("unsupported", "merged", failure=True)
    convert("unused", "typo", failure=True)
    convert("unused", "default")
    convert("unsupported", "default", failure=True)
    for case in ("unused", "multiple", "memory"):
        for mode in ("legacy", "legacy_no_heap", "selected_no_heap"):
            convert(case, mode)
    (root / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS: {len(report)} property regressions; {root}")


if __name__ == "__main__":
    main()
