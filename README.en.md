# C2BTOR

[简体中文](README.md) | English

C2Btor is a C program verification tool. It converts C programs into BTOR2, a hardware model-checking format, and reduces assertion verification to reachability checking. It supports model-checking backends including Carat, rIC3, Pono 2.0, AVR, and ABC, and can generate violation witnesses in SV-COMP YAML 2.1 format for unsafe programs.

![C2BTOR verification framework](docs/images/c2btor-framework.png)

## Dependencies

- A C++17 compiler, such as GCC.
- CMake 3.16+.
- Flex, Bison, Git, Perl, and patch.

## Build

```sh
# Configure the build directory
cmake -S . -B build

# Build C2BTOR
cmake --build build --target c2btor -j8

build/bin/c2btor --version
```

Tests are disabled by default.

## BTOR2 Modeling

```sh
build/bin/c2btor program.c --goto-btor2 --inline --32 \
  --array array --goto-btor2-out model.btor2
```

The input program should contain assertions or error-function calls. 

| Option | Purpose |
|---|---|
| `--goto-btor2` | Convert C to BTOR2 |
| `--goto-btor2-out FILE` | BTOR2 model output path |
| `--goto-btor2-map-out FILE` | Source map for witness recovery; use a separate file |
| `--32` / `--64` | C target data model: ILP32 / LP64 |
| `--inline` | Inline ordinary function calls |
| `--array bv` / `array` / `mixed` | Storage representation; Array/Mixed requires a backend with array support |

Run `build/bin/c2btor --help` for the full list of options.

## Model-Checking Backends

Install each tool using its repository instructions. The following commands check the `model.btor2` generated above.

- Carat: The original [Carat](https://github.com/youyusama/Carat) does not include the C2BTOR witness extensions.
  ```sh
  carat -a ic3 model.btor2
  ```

  For witness support, use the submodule under `checkers/carat`:
  ```sh
  git submodule update --init checkers/carat
  ```

  Follow the [witness-enabled Carat build instructions](https://github.com/westtide/carat-witness#build), then run:
  
  ```sh
  mkdir -p witness-out
  checkers/carat/build/carat -a ic3 -w witness-out/ model.btor2
  ```

  [c2btor-verify](c2btor-verify)

- rIC3: [rIC3 repository](https://github.com/gipsyh/rIC3). Use pure BV models:
  
  ```sh
  ric3 check model.btor2 portfolio
  ```

- Pono 2.0: [Pono repository](https://github.com/stanford-centaur/pono). Use Bitwuzla and IC3SA:
  
  ```sh
  pono --smt-solver bzla -e ic3sa -k 2000000000 model.btor2
  ```

- AVR:  [AVR repository](https://github.com/aman-goel/avr). For BTOR2 input, run from the AVR directory and replace the model path with its absolute path:
  
  ```sh
  python3 avr.py -o output -n example /absolute/path/model.btor2
  ```

- ABC: [ABC repository](https://github.com/berkeley-abc/abc). Use [Btor2Tools](https://github.com/hwmcc/btor2tools) to convert a pure BV model to AIGER, then run PDR. Enable `--btor2aiger` when building Btor2Tools.

  ```sh
  btor2aiger model.btor2 > model.aig
  abc -c "read_aiger model.aig; pdr"
  ```

## Literature

[BTOR2-Based C Program Verification via Hardware Model Checking](https://arxiv.org/abs/2607.17622).

## License and Acknowledgments

License texts are collected in [LICENSES/](LICENSES/). C2BTOR contributions use BSD-4-Clause. CBMC and other third-party components retain their respective licenses and notices.

We thank Daniel Kroening, Edmund Clarke, and the authors and maintainers of [CBMC/CProver](https://github.com/diffblue/cbmc), Carat, [Btor2Tools](https://github.com/hwmcc/btor2tools), the model checkers, and the witness validators.

This product includes software developed by the C2BTOR contributors.

> This product includes software developed by Daniel Kroening,
> Edmund Clarke,
> Computer Science Department, University of Oxford,
> Computer Science Department, Carnegie Mellon University.
