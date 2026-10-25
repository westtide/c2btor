# SPDX-License-Identifier: BSD-4-Clause
# SPDX-FileCopyrightText: 2026 C2BTOR contributors
"""Check a CMake converter package independently of a host C preprocessor."""
import argparse
from pathlib import Path
import subprocess
import tempfile

from scripts.btor2_parser import Btor2Model


def check(package):
    package = package.resolve()
    binary = package / "bin/c2btor"
    if not binary.is_file():
        binary = package / "bin/c2btor.exe"
    if not binary.is_file():
        raise ValueError("missing installed converter")
    notices = package / "share/doc/c2btor"
    for name in ("LICENSES/CBMC-BSD-4-Clause.txt",
                 "LICENSES/C2BTOR-BSD-4-Clause.txt",
                 "LICENSES/MiniSat-MIT.txt", "LICENSES/DownloadProject-MIT.txt"):
        if not (notices / name).is_file():
            raise ValueError("missing installed notice: " + name)
    version = subprocess.run([str(binary), "--version"], check=True,
                             capture_output=True, text=True, timeout=15).stdout.strip()
    if not version:
        raise ValueError("empty converter version")
    with tempfile.TemporaryDirectory(prefix="c2btor-package-") as directory:
        directory = Path(directory)
        # .i is preprocessed C: package smoke tests do not require a host GCC/CL.
        source = directory / "smoke.i"
        source.write_text('extern unsigned __VERIFIER_nondet_uint(void);\n'
                          'int main(void) { unsigned x=__VERIFIER_nondet_uint();\n'
                          '__CPROVER_assert(x+1U != 0U, "unsigned wrap"); }\n',
                          encoding="utf-8")
        for mode in ("bv", "array", "mixed"):
            model = directory / (mode + ".btor2")
            result = subprocess.run(
                [str(binary), str(source), "--32", "--goto-btor2", "--array", mode,
                 "--goto-btor2-out", str(model)], capture_output=True, text=True, timeout=60)
            if result.returncode:
                raise ValueError(mode + " package conversion failed:\n" + result.stderr)
            Btor2Model(model)
    print("C2BTOR " + version + ": installed notices and BV/Array/Mixed package smoke passed")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package", type=Path, required=True)
    check(parser.parse_args().package)
