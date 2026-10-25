#!/usr/bin/env bash
# SPDX-License-Identifier: BSD-4-Clause
# SPDX-FileCopyrightText: 2026 C2BTOR contributors
# Ubuntu 22.04+ prerequisites:
# sudo apt-get install build-essential cmake bison flex git perl curl patch zip file python3 python3-yaml zlib1g-dev
# git submodule update --init --recursive checkers/carat
# ./scripts/build_svcomp.sh /absolute/path/c2btor-linux-x86_64
set -euo pipefail

fail() { printf 'build_svcomp: %s\n' "$*" >&2; exit 1; }
[[ $# == 1 ]] || fail "usage: $0 OUTPUT_DIR"
[[ $(uname -s) == Linux && $(uname -m) == x86_64 ]] || fail 'build on Linux x86_64'
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
for notice in LICENSES/CBMC-BSD-4-Clause.txt LICENSES/C2BTOR-BSD-4-Clause.txt; do
    [[ -f $root/$notice ]] || fail "missing project notice: $notice"
done
carat_source="$root/checkers/carat"
[[ -f $carat_source/setup.sh ]] || fail 'initialize checkers/carat with git submodule update --init --recursive checkers/carat'
[[ ! -e $1 && ! -L $1 ]] || fail "output already exists: $1"
mkdir -p -- "$(dirname -- "$1")"
output=$(cd -- "$(dirname -- "$1")" && pwd)/$(basename -- "$1")
[[ ! -e $output.zip && ! -L $output.zip ]] || fail "archive already exists: $output.zip"
for tool in cmake make gcc g++ bison flex git perl curl patch zip python3 file strip; do
    command -v "$tool" >/dev/null || fail "missing build prerequisite: $tool"
done
python3 -c 'import yaml' || fail 'install PyYAML (Ubuntu: python3-yaml)'
modules=(__init__ btor2_parser carat cex_parser correctness source_map summary_recovery trace_recovery yaml21_writer yaml_io)
for module in "${modules[@]}"; do
    [[ -f $root/scripts/$module.py ]] || fail "missing runtime module: scripts/$module.py"
done
[[ -f $root/c2btor-verify && -f $root/scripts/requirements-witness.txt ]] || fail 'missing verifier runtime'
[[ $(git -C "$carat_source" rev-parse HEAD:deps/btor2tools) == d33c73ff1d173f1bfac8ba6b1c6d68ba62c55f8e ]] || fail 'unexpected Carat btor2tools pin; review before building'

work=$(mktemp -d "${TMPDIR:-/tmp}/c2btor-build.XXXXXX")
trap 'rm -rf -- "$work"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
export CC=/usr/bin/gcc CXX=/usr/bin/g++

# Build in a private clone: setup.sh patches dependency sources and builds SAT
# libraries in their source trees. The caller's checkout/build stay untouched.
git clone --quiet --no-hardlinks "$carat_source" "$work/carat"
git -C "$work/carat" checkout --quiet --detach "$(git -C "$carat_source" rev-parse HEAD)"
# setup.sh obtains the exact submodule and Boolector dependency revisions
# recorded by this Carat checkout, then applies its tracked patches.
JOBS=4 "$work/carat/setup.sh"
git -C "$work/carat/deps/btor2tools" apply --reverse --check "$work/carat/deps/btor2tools.patch"

# The standalone simulator uses this exact patched parser, without btor2aiger
# or Boolector. Force a fresh static parser to avoid a runtime .so dependency.
cmake -S "$work/carat/deps/btor2tools" -B "$work/btor2tools" \
    -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=OFF -DBUILD_BTOR2AIGER=OFF
cmake --build "$work/btor2tools" --target btorsim -j4
cmake -S "$work/carat" -B "$work/carat/build" -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_C_COMPILER="$CC" -DCMAKE_CXX_COMPILER="$CXX" -DUSE_LLD=OFF -DENABLE_THINLTO=OFF
cmake --build "$work/carat/build" --target carat -j4

# CMake owns the MiniSat HTTPS URL and checksum; do not duplicate the download.
cmake -S "$root" -B "$work/c2btor" -DWITH_JBMC=OFF -Denable_cbmc_tests=OFF \
    -DCMAKE_BUILD_TYPE=Release -DCMAKE_C_COMPILER="$CC" -DCMAKE_CXX_COMPILER="$CXX"
cmake --build "$work/c2btor" --target c2btor -j4

package="$work/package"
mkdir -p "$package/bin" "$package/scripts" "$package/examples" "$package/LICENSES"
install -m 755 "$root/c2btor-verify" "$package/c2btor-verify"
install -m 755 "$work/c2btor/bin/c2btor" "$package/bin/c2btor"
install -m 755 "$work/carat/build/carat" "$package/bin/carat"
install -m 755 "$work/btor2tools/bin/btorsim" "$package/bin/btorsim"
for executable in "$package/bin/"*; do
    python3 - "$executable" <<'PY'
from pathlib import Path
import sys
header = Path(sys.argv[1]).open('rb').read(20)
if len(header) != 20 or header[:6] != b'\x7fELF\x02\x01' or int.from_bytes(header[18:20], 'little') != 62:
    raise SystemExit('refusing non-ELF/x86_64 executable: ' + sys.argv[1])
PY
    strip "$executable"
    file "$executable"
done
for module in "${modules[@]}"; do
    install -m 644 "$root/scripts/$module.py" "$package/scripts/$module.py"
done
install -m 644 "$root/scripts/requirements-witness.txt" "$package/scripts/requirements-witness.txt"

# Keep project licenses and linked dependency notices in one directory.
install -m 644 "$root/LICENSES/"*.txt "$package/LICENSES/"
: > "$package/LICENSES/Runtime-Dependencies.txt"
for notice in "$work/c2btor/minisat2-src/LICENSE" \
    "$work/carat/LICENSE" "$work/carat/src/sat/minisat/LICENSE" \
    "$work/carat/src/sat/cadical/LICENSE" "$work/carat/src/sat/kissat/LICENSE" \
    "$work/carat/src/model/aiger/LICENSE" "$work/carat/deps/btor2tools/LICENSE.txt" \
    "$work/carat/deps/btor2tools/deps/boolector/COPYING" \
    "$work/carat/deps/btor2tools/deps/boolector/deps/btor2tools/LICENSE.txt" \
    "$work/carat/deps/btor2tools/deps/boolector/deps/lingeling/COPYING"; do
    [[ -f $notice ]] || fail "missing component license: $notice"
    label=${notice#"$work/"}
    label=${label#"$root/"}
    printf '\n===== %s =====\n\n' "$label" >> "$package/LICENSES/Runtime-Dependencies.txt"
    cat "$notice" >> "$package/LICENSES/Runtime-Dependencies.txt"
done

cat > "$package/examples/unsafe.c" <<'C'
extern unsigned __VERIFIER_nondet_uint(void);
extern void __VERIFIER_error(void);
int main(void) {
  unsigned a[2];
  a[0] = __VERIFIER_nondet_uint();
  a[1] = __VERIFIER_nondet_uint();
  if (a[0] == 7 && a[1] == 9)
    __VERIFIER_error();
  return 0;
}
C
cat > "$package/examples/safe.c" <<'C'
extern unsigned __VERIFIER_nondet_uint(void);
extern void __VERIFIER_error(void);
int main(void) {
  unsigned a[2];
  a[0] = __VERIFIER_nondet_uint();
  a[1] = a[0];
  if (a[0] != a[1])
    __VERIFIER_error();
  return 0;
}
C
printf '%s\n' 'CHECK( init(main()), LTL(G ! call(__VERIFIER_error())) )' > "$package/examples/unreach-call.prp"
cat > "$package/smoketest.sh" <<'SH'
#!/bin/sh
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/c2btor-smoke.XXXXXX")
trap 'rm -rf "$work"' EXIT HUP INT TERM
unset C2BTOR CARAT BTORSIM PYTHONPATH PYTHONHOME
export PYTHONNOUSERSITE=1 PYTHONDONTWRITEBYTECODE=1
for model in ILP32 LP64; do
  for name in unsafe safe; do
    directory="$work/$name-$model"
    mkdir "$directory"
    case "$name" in unsafe) expected='FALSE(unreach-call)' ;; safe) expected='TRUE' ;; esac
    if ! (cd "$directory" && "$root/c2btor-verify" "$root/examples/$name.c" \
      --property "$root/examples/unreach-call.prp" --data-model "$model" >result.log 2>&1); then
      cat "$directory/result.log"; exit 1
    fi
    if ! grep -Fqx "Verification result: $expected" "$directory/result.log"; then
      cat "$directory/result.log"; exit 1
    fi
    test -s "$directory/witness.yml"
    printf '%s %s: %s; witness generated\n' "$name" "$model" "$expected"
  done
done
SH
chmod 755 "$package/smoketest.sh"
cat > "$package/README" <<'TEXT'
C2BTOR: C to BTOR2, Carat, and SV-COMP YAML 2.1 witnesses

Requires Linux x86_64, a C compiler/preprocessor, Python 3.10+ and PyYAML.
Install the Python dependency: python3 -m pip install -r scripts/requirements-witness.txt

Run one task from its working directory:
  /path/to/c2btor-verify program.c --property unreach-call.prp --data-model ILP32
Use LP64 for 64-bit tasks. The default output is witness.yml.
An explicit output can be selected with --witness-output PATH.

The verifier races Array configurations 0, 1, 2 and 6 from Carat:
  0: -a ic3
  1: -a ic3 --ctg_max_lvl 0
  2: -a ic3 --all --ctg_max_lvl 0
  6: -a wlbmc -s kissat -k 100
The IC3 configurations use Carat's default SAT solver, minicore.
The first decisive result supplies the witness; other workers are stopped.
Bounded WLBMC without a counterexample cannot establish Safe.
In BenchExec, the 900 CPU-second allowance applies to the whole task process
tree, shared by the workers. The wrapper also has a 900-second wall backstop.
Safe witnesses retain the baseline invariant 1, not an exported Carat proof.

Report the version: ./c2btor-verify --version
Run the included ILP32/LP64 Safe/Unsafe smoke checks: ./smoketest.sh
Smoke success checks execution, result classification and witness generation;
it does not claim external witness-validator confirmation.

This product includes software developed by Daniel Kroening, Edmund Clarke,
Computer Science Department, University of Oxford,
Computer Science Department, Carnegie Mellon University.
This product includes software developed by the C2BTOR contributors.
TEXT

# Smoke checks are included for the user to run separately.
[[ ! -e $output && ! -L $output && ! -e $output.zip && ! -L $output.zip ]] || fail 'output appeared during build; refusing to overwrite'
mkdir -- "$output"
cp -a "$package/." "$output/"
(cd -- "$(dirname -- "$output")" && zip -q -r "$output.zip" "$(basename -- "$output")")
printf 'Built: %s\nArchive: %s.zip\n' "$output" "$output"
