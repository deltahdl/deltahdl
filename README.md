# DeltaHDL

DeltaHDL is an open-source SystemVerilog simulator and synthesizer written in C++23. It simulates by the event-driven algorithm and it targets IEEE 1800-2023.

## Usage

```sh
deltahdl [options] <source-files...>
```

### General Options

| Option | Description |
| --- | --- |
| `--top <module>` | Top-level module |
| `-f <file>` | Read options from file |
| `+define+<name>=<value>` | Define macro |
| `+incdir+<path>` | Include directory |
| `-Werror` | Treat warnings as errors |
| `--version` | Show version |
| `--help` | Show help |

### Simulation Options

| Option | Description |
| --- | --- |
| `--vcd <file>` | Dump VCD waveforms |
| `--seed <n>` | Random seed |
| `--lint-only` | Parse and elaborate only |
| `--dump-ast` | Print AST to stdout |
| `--dump-ir` | Print RTLIR to stdout |

### Synthesis Options

| Option | Description |
| --- | --- |
| `--synth` | Enable synthesis mode |
| `--no-opt` | Skip optimization passes |
| `--dump-aig` | Print AIG to stdout |

### Viewport Access Values

A decryption envelope's `viewport` pragma expression (IEEE 1800-2023 §34.5.32) names an object of the envelope and an access value that relaxes the object's protection. The standard leaves the access values to the implementation; DeltaHDL defines two:

| Access | Effect on the named object |
| --- | --- |
| `"r"` | A VPI application reads its properties, relationships and value as for an unprotected object, and reaches it by name through the protected scopes holding it. `vpiIsProtected` still reports TRUE. |
| `"rw"` | Everything `"r"` allows, and its value can be written. |

Any other access value draws a warning and grants nothing. The object name is resolved against the envelope's own declarations from the scope the envelope stands in. Use `"q"` for an item the envelope declares directly. Use `"secret.q"` for an item of a design element `secret` that the envelope declares; this names `q` in every instance of `secret`. A name that resolves to no declaration in the envelope is an error.

### Examples

Simulate a design with VCD output:

```sh
deltahdl --top counter --vcd waves.vcd counter.sv
```

Lint-only (parse and elaborate without simulating):

```sh
deltahdl --lint-only design.sv
```

Synthesize a design to an and-inverter graph and print its size:

```sh
deltahdl --synth --top alu alu.sv
```

Use an options file:

```sh
deltahdl -f project.args
```

Where `project.args` contains one option per line (lines starting with `#` are comments):

```text
# Project options
+incdir+src/include
+define+DEBUG=1
--top top_module
src/top.sv
src/alu.sv
```
