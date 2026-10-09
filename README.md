# C2BTOR 2.0

[English](README.md) · [简体中文](README.zh-CN.md)

## 1. C2BTOR framework

C2BTOR is a C program verification framework based on hardware model checking. It uses the [CBMC](https://github.com/diffblue/cbmc) frontend to translate C programs with assertions into Goto-IR, generates BTOR2 transition-system models, and lets different hardware model checkers search for counterexamples or prove safety properties.

![C2BTOR verification framework: C programs pass through the CBMC frontend and C2Btor encoding to produce BTOR2 models for optional hardware model checkers; SAT witnesses are replayed, translated back and independently confirmed before reporting UNSAFE; SAFE requires an unbounded proof.](docs/images/c2btor-framework.png)

**SAFE\*** requires an unbounded algorithm to prove all selected properties and model-boundary obligations. A bounded search without a counterexample does not establish SAFE.

## 2. Dependencies and installation

The source release targets **Linux x86-64**. The executable and build target are **`c2btor`**, version **`2.0.0`**. Its source baseline is `westtide/cbmc` tag `2.0`, commit `4b94c0095bfe08bfed221cb7665a225a28d18eb8`. Prebuilt converter/checker tools are not included.

- **Build:** C++17 compiler, CMake 3.8+, Make or Ninja, Flex, Bison, Git, Bash and `patch`. The default CMake configuration downloads and patches MiniSat.
- **Conversion:** a C preprocessor, such as GCC. Conversion alone does not need a model checker.
- **Verification:** install a BTOR2 backend separately, such as rIC3, Pono or BtorMC, according to its own instructions. Match array support, property handling and counterexample format to your model.
- **Optional counterexample validation:** Python 3.10+, [Btor2Tools](https://github.com/hwmcc/btor2tools) and [CPAchecker](https://github.com/sosy-lab/cpachecker). The single-task witness wrapper uses Python's standard library; `scripts/run_witness_svcomp.py` also needs PyYAML.

On Ubuntu/Debian:

```sh
sudo apt-get update
sudo apt-get install build-essential cmake ninja-build flex bison patch git
git clone https://github.com/westtide/c2btor.git
cd c2btor
cmake -S . -B build -G Ninja -DWITH_JBMC=OFF -DCMAKE_BUILD_TYPE=Release
cmake --build build --target c2btor -j4
build/bin/c2btor --version
```

Run commands from the repository root. JBMC is not included, so keep `WITH_JBMC=OFF`. Reduce `-j4` on machines with limited memory. The executable is `build/bin/c2btor`. The default dependency download needs network access; if your system supplies MiniSat headers and a library, configure a separate build with `-Dsat_impl=system-minisat2`.

For an optional local installation:

```sh
cmake --install build --component c2btor --prefix /path/to/install
```

## 3. Supported hardware model checkers

| Tool | Input path | Notes |
| --- | --- | --- |
| [rIC3](https://github.com/gipsyh/rIC3) | BTOR2 / AIGER | IC3, BMC and other algorithms; this repository provides runner scripts. |
| [Pono](https://github.com/stanford-centaur/pono) | BTOR2 | Multiple SMT-based model-checking algorithms; follow the tool's official usage instructions. |
| [BtorMC](https://github.com/Boolector/boolector) | BTOR2 | Bounded model checking; standard counterexamples have been used for replay validation. |
| [AVR](https://github.com/aman-goel/avr) | BTOR2 | A format-compatible backend; C2BTOR's end-to-end witness path has not been independently validated with it. |
| [SimpleCAR](https://github.com/lijwen2748/simplecar), [ABC](https://github.com/berkeley-abc/abc) | BTOR2 → AIGER | Bit-level model checking; use a pure BV encoding and install a converter. |

Match the model's arrays, property count and counterexample format to the chosen backend. Other compatible BTOR2/AIGER checkers can also be connected.

## 4. Parameters and commands

### Convert a C program

For a program containing its own assertions, use:

```sh
mkdir -p work
build/bin/c2btor program.c --goto-btor2 --inline --64 \
  --goto-btor2-out work/model.btor2 \
  --goto-btor2-map-out work/model.map.json \
  --memory object --array bv \
  --no-standard-checks --no-pointer-check \
  --no-bounds-check --no-built-in-assertions
```

Replace `program.c` with your source file. Choose `--32` for an ILP32 task or `--64` for Linux LP64; the choice describes the C target, not the host executable's bitness. `--inline` expands ordinary helper calls. The `--no-*` flags disable CBMC's automatically added checks while retaining source assertions; C2BTOR's own memory and model-limit diagnostics remain.

If Btor2Tools is installed, run `catbtor work/model.btor2` to check syntax and types. Model generation and parsing do not themselves prove the source program safe.

### Parameter reference

Pass values with spaces, for example `--memory object`. Use the BTOR2 encoding/property options with `--goto-btor2`.

| Parameter | Meaning and use |
| --- | --- |
| `--goto-btor2` | Enable C-to-BTOR2 conversion. |
| `--goto-btor2-out FILE` | Save the model; default output is stdout. |
| `--goto-btor2-map-out FILE` | Save model/GotoIR/C locations, property metadata and model obligations. Use a different file from the model. |
| `--memory object` / `--memory global` | Use independent object storage or one global memory store. Default: `object`. |
| `--array bv` / `--array array` | Use bitvectors or BTOR2 array read/write storage. Default: `bv`; array encoding requires a backend that supports arrays. |
| `--memory-object-max-bytes N` | Explicitly cap runtime object capacity in object mode. By default, capacity is inferred from the final GotoIR. Exceeding a cap is a model limit, not malloc failure. |
| `--array-bv-max-object-bytes N` | Set the runtime capacity cap for BV storage. If both capacity options are set in object/BV mode, their values must agree. |
| `--goto-btor2-heap-objects K` | Bound total successful dynamic allocations; default `32`. Freeing an object does not return its identity to this budget. |
| `--malloc-may-fail --malloc-fail-null` | Include the branch where allocation fails and returns NULL. |
| `--goto-btor2-checks` | Insert selected CBMC safety checks before encoding; combine with flags such as `--bounds-check`, `--pointer-check` or `--div-by-zero-check`. |
| `--goto-btor2-error-function NAME` | Mark calls to an error function as unreach-call properties before inlining; combine with `--inline`. |
| `--goto-btor2-reach-only` | Select only that error function's source properties; requires `--goto-btor2-error-function NAME`. |
| `--goto-btor2-merge-bads` | OR the selected source assertion bads into one. Alias: `--goto-btor2-merge-properties`. Auxiliary diagnostics are separate. |
| `--goto-btor2-no-heap-guards` | Hide auxiliary memory/model-limit bad reports while preserving path freezing and proof obligations. A source UNSAT result alone does not discharge hidden obligations. |

Fixed objects use their actual size. Runtime object capacity is finite and planned when the model is generated; it does not grow during solving. For example, request only array bounds instrumentation with `--no-standard-checks --bounds-check --goto-btor2-checks`.

### Check an error function

For a program that defines/calls `reach_error`, select its reachability property with:

```sh
build/bin/c2btor program.c --goto-btor2 --inline --64 \
  --memory object --array bv \
  --goto-btor2-error-function reach_error \
  --goto-btor2-reach-only --goto-btor2-merge-bads \
  --goto-btor2-out work/reach.btor2 \
  --goto-btor2-map-out work/reach.map.json \
  --no-standard-checks --no-pointer-check \
  --no-bounds-check --no-built-in-assertions
```

This combines the selected source properties. If a backend needs a single bad, adding `--goto-btor2-no-heap-guards` also hides auxiliary bads, but the associated obligations must still be checked before claiming C safety. A bounded search without a counterexample is not an unbounded SAFE proof; TIMEOUT and UNKNOWN give no safety conclusion.

### Export a hash-bound source map

To prepare the same `reach_error` program for witness translation:

```sh
cat > work/reach.prp <<'EOF'
CHECK( init(main()), LTL(G ! call(reach_error())) )
EOF
python3 scripts/c2btor_witness.py export \
  --c2btor build/bin/c2btor --program program.c --spec work/reach.prp \
  --output-dir work/witness-export -- --64
```

The final output directory must be new. Export creates a model and source/model hash-bound map; it does not run a solver or generate a counterexample. The maintained counterexample path is standard BTOR2 witness → BtorSim replay → SV-COMP violation YAML 2.0 → CPAchecker confirmation. Memory validity and model-limit traces are classified separately from source error-call violations. SAFE invariant witnesses are not generated.

For the complete interfaces, run `build/bin/c2btor --help` and `python3 scripts/c2btor_witness.py --help`. Conversion regression scripts remain in `regression/goto-btor2/`; supply separately installed tools as described by each script's `--help`.

### Supported scope

The converter supports sequential programs starting at `main`, ordinary function calls after inlining, machine integers, supported binary32/binary64 floating-point operations, and finite object memory. Recursive call stacks, concurrency, unbounded heaps, and some C memory operations remain unsupported. A program accepted by the CBMC frontend may still be outside C2BTOR's encoding scope.

## 5. Acknowledgements and license

**C2BTOR is built on CBMC.** We thank Daniel Kroening, Edmund Clarke, the CBMC/CProver authors and all upstream contributors for the C frontend, GotoIR, target configuration and program transformations that make this framework possible. See the [CBMC source repository](https://github.com/diffblue/cbmc) and [official documentation](https://diffblue.github.io/cbmc/).

We also thank the authors and maintainers of Btor2Tools, the hardware model checkers and CPAchecker.

The imported source retains the [4-clause BSD license](LICENSE) and file-specific notices. [LICENSE.c2btor](LICENSE.c2btor) preserves this repository's original BSD 3-Clause notice and does not replace the upstream terms. Upstream binary-reader test inputs are retained as test fixtures; they are not prebuilt converter/checker releases.

> This product includes software developed by Daniel Kroening,
> Edmund Clarke,
> Computer Science Department, University of Oxford,
> Computer Science Department, Carnegie Mellon University.
