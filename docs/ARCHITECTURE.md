# Architecture

DeltaHDL compiles SystemVerilog source files through a staged pipeline. Each
stage transforms the design into a progressively lower-level representation
until it reaches either a running simulation or a mapped netlist.

```text
Source Files (.sv)
       |
       v
+--------------+
| Preprocessor |   macro expansion, `include, `ifdef
+--------------+
       |
       v
+-------+
| Lexer |          tokenization (IEEE 1800-2023 section 5)
+-------+
       |
       v
+--------+
| Parser |         recursive-descent + Pratt expression parsing
+--------+
       |
       v
  CompilationUnit (AST)
       |
       v
+-------------+
| Elaborator  |    type checking, constant folding, sensitivity analysis
+-------------+
       |
       v
  RtlirDesign (RTLIR)
       |
       +---------------------------+
       |                           |
       v                           v
  Simulation Path             Synthesis Path
```

## Compilation Pipeline

### Preprocessor

The preprocessor handles macro definitions (`+define+`), file inclusion
(`` `include ``), and conditional compilation (`` `ifdef ``/`` `ifndef ``). It
operates on raw source text before tokenization and produces a single
concatenated string for the lexer. Include directories are specified with
`+incdir+`.

### Lexer

A hand-written lexer converts the preprocessed source text into a token stream.
It recognizes all IEEE 1800-2023 keywords, operators, literals, and system
identifiers. The lexer attaches source locations to every token so that
downstream diagnostics can point back to the original file and line.

### Parser

A recursive-descent parser consumes the token stream and builds an abstract
syntax tree (AST). Expressions use a Pratt parser for correct precedence and
associativity. The AST is allocated in an arena so that the entire tree can
be freed in one shot after elaboration.

The top-level AST node is a `CompilationUnit` containing modules, packages,
and interfaces.

### Elaborator

The elaborator walks the AST, resolves types, evaluates constant expressions,
and produces a register-transfer level intermediate representation (RTLIR).
It performs sensitivity analysis to determine which signals each `always`
block depends on.

The RTLIR consists of `RtlirModule` nodes containing ports, nets, variables,
continuous assignments, and processes. Each process carries its sensitivity
list and body statement.

After elaboration the pipeline branches into either simulation or synthesis.

## Simulation

```text
RtlirDesign
     |
     v
+----------+
| Lowerer  |      creates Variables, Nets, and coroutine Processes
+----------+
     |
     v
SimContext + Scheduler
     |
     v
+------------------+
| Event Scheduler  |   17-region stratified loop (IEEE section 4.5)
+------------------+
     |
     v
+-----------+      +------------+
| VcdWriter |      | VPI / DPI  |   waveform output, foreign interfaces
+-----------+      +------------+
```

### Lowerer

The lowerer translates an `RtlirDesign` into runtime simulation objects. For
each RTLIR variable it creates a `Variable` in the `SimContext`. For each
RTLIR process it creates either a coroutine `Process` or a `CompiledProcess`
depending on whether the body contains timing controls.

### SimContext

`SimContext` owns the simulation state: variables, nets, the scheduler, and
auxiliary contexts (VPI, DPI, clocking, assertions). It provides lookup by
name and scope management for function calls.

### Event Scheduler

The scheduler implements the IEEE 1800-2023 section 4.5 stratified event
algorithm. Each simulation timestep is divided into 17 ordered regions:

```text
  Preponed
  PreActive
  Active           <--+
  Inactive            |  active iteration loop
  PreNBA              |
  NBA                 |
  PostNBA          ---+
  PreObserved
  Observed         <--+
  PostObserved        |  reactive iteration loop
  Reactive            |
  ReInactive          |
  PreReNBA            |
  ReNBA               |
  PostReNBA        ---+
  PrePostponed
  Postponed
```

Events are stored in a calendar keyed by `SimTime`. Within a timestep the
scheduler drains each region in order, iterating the active and reactive
sets until they stabilize before advancing.

Events are allocated from an `EventPool` backed by an arena allocator. Used
events are recycled through a free-list to avoid per-event allocation
overhead.

### Process Model

Processes that contain timing controls (`#delay`, `@(posedge clk)`, `wait`)
run as C++23 coroutines. Each `co_await` suspends the coroutine and schedules
a resume event in the appropriate region. Processes without timing controls
are compiled into plain `std::function` lambdas for lower overhead.

### Four-Value Logic

All simulation values use dual-rail aval/bval encoding per the VPI convention:

```text
  Value   aval  bval
  -----   ----  ----
    0       0     0
    1       1     0
    x       0     1
    z       1     1
```

Values are packed into 64-bit words. A `Logic4Vec` holds a width and a
pointer to an arena-allocated array of `Logic4Word` structs.

### Variables and Nets

A `Variable` stores a `Logic4Vec` value and a list of watcher callbacks.
When a value changes, `NotifyWatchers` moves the callback list, clears it,
and executes each callback exactly once (one-shot semantics). Persistent
watchers must re-register themselves after firing.

A `Net` extends `Variable` with strength-aware resolution. Each driver
contributes a value and strength pair, and the net resolves them according
to the IEEE resolution rules.

### VCD Writer

The VCD writer records signal changes during simulation and writes them in
Value Change Dump format. It registers itself as a post-timestep callback on
the scheduler so that changed values are flushed after each time advance.

### VPI

The Verilog Procedural Interface (VPI) exposes simulation objects to external
C code through the standard `vpi_*` function set. `VpiContext` attaches to a
`SimContext`, builds an object map of all variables, and supports handle
lookup, iteration, value get/put, and value-change callbacks.

### DPI-C

The Direct Programming Interface allows SystemVerilog code to call C functions
(imports) and C code to call SystemVerilog functions (exports). The
`DpiContext` maps import names to native function pointers and dispatches
calls from the expression evaluator.

### Compiled Simulation

Processes without timing controls can be compiled into a tree of
`std::function` lambdas at elaboration time. The `ProcessCompiler` walks
the AST body and produces a `CompiledProcess` whose `Execute` method runs
the compiled lambda directly, bypassing the coroutine machinery.

### Multi-Threaded Simulation

The `Partitioner` performs dependency analysis on compiled processes. It
groups non-conflicting processes (those that do not share written signals)
into partitions. The `MtScheduler` executes independent partitions in
parallel using `std::jthread`, while conflicting partitions run sequentially.

### Clocking Blocks

`ClockingManager` implements IEEE clocking block semantics. On a clock edge
it samples input signals and stores their values. Output drives are scheduled
with skew delays as NBA-region events.

### Concurrent Assertions

`AssertionMonitor` evaluates SVA-style properties on signal changes. It
registers watchers on monitored signals and schedules evaluation events in
the Observed region. Properties like `$rose`, `$fell`, and `$stable` are
checked each cycle.

## Synthesis

```text
RtlirDesign
     |
     v
+-------------+
| SynthLower  |    convert RTLIR to And-Inverter Graph
+-------------+
     |
     v
+----------+
| AIG Opts |       ConstProp, Balance, Rewrite
+----------+
     |
     v
+---------+        +----------+
| LUT Map |        | Cell Map |   technology mapping
+---------+        +----------+
     |
     v
+----------------+
| NetlistWriter  |   BLIF, Verilog, JSON, EDIF output
+----------------+
```

### SynthLower

The synthesis lowerer converts an `RtlirModule` into an And-Inverter Graph
(AIG). Combinational logic maps directly to AND/NOT nodes. Sequential
elements become AIG latches.

### AIG Optimization

Three optimization passes run over the AIG:

- **ConstProp** eliminates nodes with constant inputs.
- **Balance** restructures the graph to minimize depth.
- **Rewrite** applies local rewriting rules to reduce node count.

### Technology Mapping

LUT mapping partitions the AIG into K-input lookup tables using a
depth-optimal cut enumeration algorithm. Cell mapping matches LUT clusters
against a Liberty timing library to produce technology-specific cells.

### Memory Inference

The memory inference pass detects array access patterns in the RTLIR and
replaces them with dedicated memory primitives before AIG lowering.

### Netlist Writer

The netlist writer serializes the mapped design into one of four output
formats: BLIF, structural Verilog, JSON, or EDIF.

## Source Layout

```text
src/
  common/          types, diagnostics, arena allocator, source manager
  lexer/           tokenizer, keyword table
  preprocessor/    macro expansion, conditional compilation
  parser/          recursive-descent parser, Pratt expression parser, AST
  elaboration/     type checking, constant eval, sensitivity, RTLIR
  simulation/      scheduler, processes, eval, VCD, clocking
  vpi/             VPI object model, DPI context, svdpi.h, vpi_user.h
  synthesis/       AIG, optimization, LUT/cell mapping, netlist output
  main.cpp         CLI entry point

test/
  unit/            Google Test unit tests (one per source module)
  integration/     E2E simulation tests with .expected output files

scripts/
  run_sim_tests.py    E2E test runner
  run_sv_tests.py     sv-tests integration runner
```

## Design Decisions

**Hand-written frontend.** The lexer and parser are written by hand rather
than generated by tools like flex, bison, or ANTLR. This gives full control
over error recovery and diagnostic quality.

**Arena allocation.** Each compilation phase uses its own arena allocator.
AST nodes, RTLIR nodes, and simulation events are all arena-allocated. This
eliminates per-object `delete` calls and makes phase cleanup a single
deallocation.

**Coroutines for processes.** C++23 coroutines model `always` blocks
naturally: each `co_await` maps to a timing control. The scheduler resumes
coroutines by scheduling events, so the process suspension and resume
mechanism is the same as the event dispatch mechanism.

**Dual-rail encoding.** The aval/bval representation matches the VPI
standard encoding. This means VPI get/put operations require no value
conversion, and four-value arithmetic maps to bitwise operations on the
two rails.
