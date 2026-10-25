# C2BTOR 2.0

[English](README.md) · [简体中文](README.zh-CN.md)

## 1. C2BTOR framework

C2BTOR is a C program verification framework based on hardware model checking. It uses the [CBMC](https://github.com/diffblue/cbmc) frontend to translate C programs with assertions into Goto-IR, generates BTOR2 transition-system models, and lets hardware model checkers search for counterexamples or prove safety properties.

![C2BTOR framework: the CBMC frontend, Goto-IR and C2BTOR encoding in C2Btor-dev produce BTOR2, optionally converted to AIGER. Counterexamples are replayed, translated and independently confirmed before UNSAFE; SAFE requires a complete unbounded proof.](docs/images/c2btor-framework.png)

**C2Btor-dev** identifies the conversion components in the [development repository](https://github.com/westtide/C2Btor-dev). Its C frontend still comes from CBMC; renaming the repository does not change the frontend's origin.

**SAFE\*** requires an unbounded algorithm to prove all selected properties and model-boundary obligations. Bounded absence of a counterexample does not establish SAFE. The independent validator is a separate confirmation step; generating a witness is not independent validation.

## 2. Dependencies and installation

This source release targets **Linux x86-64**. The converter and build target are **`c2btor`**, version **`2.0.0`**, with the **CBMC 6.11.0** frontend. This update imports `westtide/C2Btor-dev` commit [`4e617cf2ea95c1e70f5b7598fdba04e4284dd215`](https://github.com/westtide/C2Btor-dev/commit/4e617cf2ea95c1e70f5b7598fdba04e4284dd215). The repository contains source; model checkers must be built or installed separately.

- **Build:** C++17 compiler, CMake 3.16+, Make or Ninja, Flex, Bison, Git, Perl, Bash and `patch`. The default configuration downloads and builds MiniSat.
- **Conversion:** a C preprocessor such as GCC. Conversion alone needs no model checker.
- **Optional verification and witnesses:** install a backend separately. Witness translation also needs Python 3.10+, PyYAML, witness-enabled Carat and the matching BtorSim. Configure an independent validator separately.

On Ubuntu/Debian, run from the repository root:

```sh
sudo apt-get update
sudo apt-get install build-essential cmake ninja-build flex bison patch git perl python3-venv
git clone https://github.com/westtide/c2btor.git
cd c2btor
cmake -S . -B build -G Ninja -DCMAKE_BUILD_TYPE=Release
cmake --build build --target c2btor -j4
build/bin/c2btor --version
```

By default, only the product and its dependencies are built. JBMC is not included. Reduce `-j4` on machines with limited memory. Dependency downloads require network access; if the system supplies MiniSat headers and a library, configure a separate build with `-Dsat_impl=system-minisat2`.

Optional converter installation:

```sh
cmake --install build --component c2btor --prefix /path/to/install
```

The component installs the converter, completion, bilingual README files, figure and notices. Prepare the full witness toolchain separately:

```sh
git submodule update --init --recursive checkers/carat
python3 -m venv .venv
.venv/bin/pip install -r scripts/requirements-witness.txt
```

`checkers/carat` is a pinned **Carat source submodule**, without prebuilt checkers. It is optional for BTOR2 generation alone. Build Carat and the matching BtorSim using the [witness-enabled Carat instructions](https://github.com/westtide/carat-witness#build). The verifier searches repository build directories and `PATH`; select tools explicitly with `C2BTOR`, `CARAT` and `BTORSIM` environment variables.

## 3. Supported hardware model checkers

| Tool | Input path | Notes |
| --- | --- | --- |
| [Witness-enabled Carat](https://github.com/westtide/carat-witness) | BTOR2 | Backend used by `c2btor-verify`; produces standard counterexamples for YAML 2.1 translation. Original Carat lacks these witness extensions. |
| [rIC3](https://github.com/gipsyh/rIC3) | BTOR2 / AIGER | IC3, BMC and other algorithms; use pure BV models for this release's rIC3 path. |
| [Pono](https://github.com/stanford-centaur/pono) | BTOR2 | Multiple SMT-based algorithms; select a solver and engine using its official instructions. |
| [BtorMC](https://github.com/Boolector/boolector) | BTOR2 | Bounded model checking; absence of a counterexample covers only the searched bound. |
| [AVR](https://github.com/aman-goel/avr) | BTOR2 | Format-compatible backend; its end-to-end witness path was not independently validated for this update. |
| [SimpleCAR](https://github.com/lijwen2748/simplecar), [ABC](https://github.com/berkeley-abc/abc) | BTOR2 → AIGER | Bit-level checking; use pure BV encoding and convert with `btor2aiger` first. |

Match arrays, property count and counterexample format to the backend. Do not pass `array` / `mixed` models to backends without array support. Other compatible BTOR2/AIGER checkers can also be connected.

## 4. Parameters and commands

### Convert a C program with assertions

```sh
mkdir -p work
cat > work/program.c <<'EOF'
extern unsigned __VERIFIER_nondet_uint(void);
int main(void)
{
  unsigned x = __VERIFIER_nondet_uint();
  __CPROVER_assert(x + 1U != 0U, "unsigned wrap");
}
EOF
build/bin/c2btor work/program.c --goto-btor2 --inline --32 \
  --array bv --goto-btor2-out work/model.btor2 \
  --goto-btor2-map-out work/model.map.json
```

Choose `--32` for ILP32 or `--64` for Linux LP64; these describe the C target data model. Models and maps must use different files, and existing output files are protected from overwriting. Run `catbtor work/model.btor2` to check syntax and types. Parsing does not prove the source program safe.

### Parameter reference

Pass values with spaces. Do not supply contradictory flags or different repeated representation values.

| Parameter | Meaning and use |
| --- | --- |
| `--goto-btor2` | Enable C-to-BTOR2 conversion. |
| `--goto-btor2-out FILE` / `--goto-btor2-map-out FILE` | Set the model and witness source-map files separately. |
| `--inline` | Inline ordinary function calls. |
| `--32` / `--64` | Select the ILP32 / LP64 C target data model. |
| `--memory object` / `--memory global` | Use independent object storage or global memory; default `object`. |
| `--array bv` / `--array array` / `--array mixed` | Select BV, Array or Mixed storage; default `bv`. Mixed requires object memory. |
| `--array-mixed-threshold-bits N` | Object-size threshold for Mixed storage, in bits; default `2048`. |
| `--goto-btor2-merge-bads` | OR selected source bads together; enabled by default. Disable with `--goto-btor2-no-merge-bads`. |
| `--goto-btor2-checks` | Explicitly instrument selected CBMC checks; combine with `--bounds-check`, `--pointer-check`, `--div-by-zero-check`, etc. |
| `--goto-btor2-optimize-state` | Optimize before encoding and prune unobservable states; enabled by default. Disable with `--goto-btor2-no-optimize-state`. |
| `--goto-btor2-no-array-optimizations` | Restore the earlier opt-in behavior of Array/Mixed optimization stages for comparison. |
| `--memory-object-max-bytes N` | Explicit object-capacity cap; automatic by default. Insufficient capacity rejects conversion. |
| `--goto-btor2-heap-objects K` | Object-storage slot limit; default or `0` means infer automatically. Insufficient slots reject conversion. |

Conversion does not instrument CBMC standard checks by default: source assertions and standard SV-COMP error calls become properties. The old `--no-standard-checks` and related flags remain compatibility options in BTOR2 mode. Use the current `build/bin/c2btor --help`; do not reuse retired error-function, reach-only or no-heap-guards commands.

### Run a model checker

Choose a path for an installed tool to check the pure BV model above:

```sh
ric3 check work/model.btor2 portfolio
carat -a ic3 work/model.btor2
btor2aiger work/model.btor2 > work/model.aig
abc -c "read_aiger work/model.aig; pdr"
```

`btor2aiger` comes from [Btor2Tools](https://github.com/hwmcc/btor2tools); enable the converter when building that package. Successful conversion, bounded absence of a counterexample, UNKNOWN and timeout are not SAFE proofs.

### Generate a YAML 2.1 witness

Create a program that calls `reach_error` and its property file:

```sh
cat > work/reach.c <<'EOF'
extern unsigned __VERIFIER_nondet_uint(void);
void reach_error(void) { __CPROVER_assert(0, "error reached"); }
int main(void)
{
  if(__VERIFIER_nondet_uint() == 10U) reach_error();
  return 0;
}
EOF
cat > work/reach.prp <<'EOF'
CHECK( init(main()), LTL(G ! call(reach_error())) )
EOF
.venv/bin/python c2btor-verify work/reach.c --property work/reach.prp \
  --data-model ILP32 --witness-output work/witness.yml \
  --keep-intermediates work/verify-run
```

The witness file and intermediates directory must be new. This entry point uses object + Array encoding, races four Carat configurations, and replays/translates Unsafe traces with BtorSim before writing YAML 2.1. It does not automatically invoke an independent validator. Confirm candidate witnesses separately. The current Safe path writes an invariant of `1`, which is not an independent safety certificate.

See `build/bin/c2btor --help` and `.venv/bin/python c2btor-verify --help` for the full interfaces.

### Build and run focused tests

```sh
.venv/bin/pip install -r scripts/tests/requirements.txt
cmake -S . -B build-tests -G Ninja -Denable_cbmc_tests=ON \
  -DPython3_EXECUTABLE="$PWD/.venv/bin/python"
cmake --build build-tests -j4
ctest --test-dir build-tests --output-on-failure
```

Tests cover focused C2BTOR, C frontend and GOTO-IR C++ cases, plus Python/CLI/witness checks. Some integration cases skip when external tools are unavailable. Conversion or finite-trace checks do not replace unbounded proofs.

## 5. Acknowledgements and license

**C2BTOR is built on CBMC.** We thank Daniel Kroening, Edmund Clarke, the CBMC/CProver authors and all upstream contributors for the C frontend, Goto-IR, target configuration and program transformations. See the [CBMC source](https://github.com/diffblue/cbmc) and [official documentation](https://diffblue.github.io/cbmc/). We also thank the authors and maintainers of Carat, Btor2Tools, the model checkers, witness validators and other dependencies.

Source retains the C2BTOR BSD-4-Clause, CBMC and third-party notices in [LICENSES/](LICENSES/). Root [LICENSE](LICENSE) and [LICENSE.c2btor](LICENSE.c2btor) preserve this publication repository's existing notices and do not replace component-specific terms.

This product includes software developed by the C2BTOR contributors.

> This product includes software developed by Daniel Kroening,
> Edmund Clarke,
> Computer Science Department, University of Oxford,
> Computer Science Department, Carnegie Mellon University.
