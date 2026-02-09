# DeltaHDL

DeltaHDL is an open-source event-driven SystemVerilog IEEE 1800-2023 simulator and synthesizer written in C++23.

## Building

Requires CMake 3.28+ and a C++23 compiler (Clang 18+ or GCC 14+).

```sh
cmake -B build
cmake --build build --parallel
```

## Usage

```
deltahdl [options] <source-files...>
```

### General Options

| Option | Description |
|---|---|
| `-o <name>` | Set output name |
| `--top <module>` | Top-level module |
| `-f <file>` | Read options from file |
| `-v <file>` | Verilog library file |
| `-y <dir>` | Verilog library directory |
| `+define+<name>=<value>` | Define macro |
| `+incdir+<path>` | Include directory |
| `-Wall` | Enable all warnings |
| `-Werror` | Treat warnings as errors |
| `--version` | Show version |
| `--help` | Show help |

### Simulation Options

| Option | Description |
|---|---|
| `--vcd <file>` | Dump VCD waveforms |
| `--fst <file>` | Dump FST waveforms |
| `--max-time <time>` | Maximum simulation time |
| `--seed <n>` | Random seed |
| `--timescale <t/p>` | Override default timescale |
| `--lint-only` | Parse and elaborate only |
| `--dump-ast` | Print AST to stdout |
| `--dump-ir` | Print RTLIR to stdout |

### Synthesis Options

| Option | Description |
|---|---|
| `--synth` | Enable synthesis mode |
| `--target <name>` | Target technology |
| `--lut-size <n>` | LUT input count (default 4) |
| `--lib <file>` | Liberty timing library |
| `--format <fmt>` | Output format: `blif`, `verilog`, `json`, `edif` |
| `--no-opt` | Skip optimization passes |
| `--area` | Area-oriented optimization |
| `--delay` | Delay-oriented optimization |
| `--retime` | Enable register retiming |
| `--dump-aig` | Print AIG to stdout |

### Examples

Simulate a design with VCD output:

```sh
deltahdl --top counter --vcd waves.vcd counter.sv
```

Lint-only (parse and elaborate without simulating):

```sh
deltahdl --lint-only design.sv
```

Synthesize to BLIF:

```sh
deltahdl --synth --format blif --top alu alu.sv
```

Use an options file:

```sh
deltahdl -f project.args
```

Where `project.args` contains one option per line (lines starting with `#` are comments):

```
# Project options
+incdir+src/include
+define+DEBUG=1
--top top_module
src/top.sv
src/alu.sv
```

## Testing

```sh
cmake --build build --parallel
ctest --test-dir build --output-on-failure
```

The testing pyramid consists of:

- **Unit tests** (Google Test) under `test/unit/` test individual components.
- **Integration tests** use [CHIPS Alliance sv-tests](https://github.com/chipsalliance/sv-tests) for conformance via `scripts/run_sv_tests.py`.
- **E2E tests** under `test/integration/` run full simulations and compare output against `.expected` files via `scripts/run_sim_tests.py`.

## License

GPL-3.0. See [LICENSE](LICENSE).
