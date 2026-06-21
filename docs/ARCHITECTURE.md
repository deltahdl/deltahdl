# Architecture

## Table of Contents

1. [Introduction](#introduction)
2. [Front End](#front-end)
   1. [Preprocessor](#preprocessor)
   2. [Lexer](#lexer)
   3. [Parser](#parser)
   4. [Elaborator](#elaborator)
3. [Back End](#back-end)
   1. [Simulator](#simulator)
      1. [Lowerer](#lowerer)
      2. [Scheduler](#scheduler)
      3. [Evaluator](#evaluator)
   2. [Synthesizer](#synthesizer)
      1. [Synth Lowerer](#synth-lowerer)
      2. [Optimizer](#optimizer)
      3. [Mapper](#mapper)
      4. [Writer](#writer)
4. [Appendices](#appendices)
   1. [Appendix A: Design Decisions](#appendix-a-design-decisions)
   2. [Appendix B: Abbreviations](#appendix-b-abbreviations)
   3. [Appendix C: Glossary](#appendix-c-glossary)

## Introduction

DeltaHDL compiles SystemVerilog source files through a staged pipeline. The
front end (Preprocessor through Elaborator) is shared. The Elaborator
produces a Register-Transfer Level Intermediate Representation (RTLIR), which
is a simplified model of the design containing ports, nets, variables,
assignments, and processes with resolved types and evaluated parameters.
After elaboration the user selects either simulation or synthesis, and the
corresponding Lowerer translates the RTLIR into the structures needed by
that back end.

```text
  Simulation mode:              Synthesis mode:

  ┌────────────────┐            ┌────────────────┐
  │  Preprocessor  │            │  Preprocessor  │
  └───────┬────────┘            └───────┬────────┘
          │                             │
          ▼                             ▼
     ┌─────────┐                   ┌─────────┐
     │  Lexer  │                   │  Lexer  │
     └────┬────┘                   └────┬────┘
          │                             │
          ▼                             ▼
    ┌──────────┐                  ┌──────────┐
    │  Parser  │                  │  Parser  │
    └─────┬────┘                  └─────┬────┘
          │                             │
          ▼                             ▼
  ┌──────────────┐              ┌──────────────┐
  │  Elaborator  │              │  Elaborator  │
  └──────┬───────┘              └──────┬───────┘
         │                             │
         ▼                             ▼
    ┌───────────┐               ┌──────────────┐
    │ Simulator │               │ Synthesizer  │
    └───────────┘               └──────────────┘
```

Figure 1: Compilation pipeline for simulation and synthesis modes.

## Front End

### Preprocessor

The preprocessor handles macro definitions (`+define+`, `` `define ``/`` `undef ``),
file inclusion (`` `include ``), and conditional compilation
(`` `ifdef ``/`` `ifndef ``/`` `elsif ``/`` `else ``). It operates on raw source
text before tokenization and produces a single concatenated string for the
lexer. Include directories are specified with `+incdir+`. It also processes the
remaining standard compiler directives — `` `line ``,
`` `celldefine ``/`` `endcelldefine ``, `` `unconnected_drive ``,
`` `default_decay_time ``, `` `default_trireg_strength ``, the `` `delay_mode_* ``
family, and `` `begin_keywords ``/`` `end_keywords `` — and tracks the resulting
state (`` `timescale ``, `` `default_nettype ``, unconnected-drive net type,
decay time, trireg strength, and delay mode), propagating it to the parser
through the preprocessed result.

The macro table supports both object-like and function-like macros with
default argument values. Predefined macros such as `__FILE__` and `__LINE__`
are available. Circular inclusion is detected and reported as an error.

### Lexer

A hand-written lexer converts the preprocessed source text into a token stream.
It recognizes all IEEE 1800-2023 keywords, operators, literals, and system
identifiers. The keyword table supports version-aware recognition so that
keywords introduced in later revisions of the standard can be selectively
enabled or disabled. The lexer attaches source locations to every token so that
downstream diagnostics can point back to the original file and line. String
literal escape sequences are handled during tokenization. A keyword-version
stack supports nested `` `begin_keywords ``/`` `end_keywords `` blocks, and FSM
tool pragmas embedded in block comments are extracted during tokenization for
use by functional-coverage reporting.

### Parser

A recursive-descent parser consumes the token stream and builds an abstract
syntax tree (AST). Expressions use a Pratt parser for correct precedence and
associativity. The parser is split across several translation units organized
by grammar domain: top-level declarations (modules, packages, interfaces,
programs, classes, checkers, user-defined primitives), type and variable
declarations, statements, module instantiation, port lists, assertions,
sequence and property declarations, specify blocks, clocking blocks, generate
constructs, verification constructs (randcase, randsequence), `let` and `bind`
declarations, DPI import/export, and configuration declarations. A separate
unit handles time-literal resolution.

The AST is allocated in an arena so that the entire tree can be freed in one
shot after elaboration. The top-level AST node is a `CompilationUnit`. Besides
modules, packages, interfaces, programs, and classes, it holds user-defined
primitives, checkers, configurations, library declarations, bind directives,
external constraint blocks, and compilation-unit-scope items.

### Elaborator

The elaborator walks the AST and produces the RTLIR. It takes the general
description the Parser produced and turns it into a fully detailed one. The
Parser accepts code where widths depend on parameters, where blocks of code
may or may not exist depending on conditions, and where types are referenced
by name without their full definition inline. The Elaborator fills all of that
in. When it finishes, every signal has a known width, every conditional block
has been decided, every type reference has been replaced with its full
definition, and every process knows exactly which signals it watches.

It is assisted by three sub-passes. The type evaluator resolves data types
including structs, unions, enums, and typedefs, computing widths and sign
information. The constant evaluator folds expressions whose values can be
determined at compile time, which is essential for parameter resolution and
generate-block expansion. The sensitivity analyzer determines which signals
each `always` block depends on and constructs the corresponding event
expressions.

During elaboration, generate blocks (`if`, `for`, `case`) are expanded
according to parameter values. Module instantiations are recursively
elaborated, binding ports and applying parameter overrides. A separate pass
resolves `defparam` overrides after the module hierarchy has been constructed.
A validation pass checks constraints such as assignment to constants and
enum type compatibility.

Beyond core RTL, the elaborator carries out the semantic analysis and
validation needed by the advanced and verification feature set: concurrent
assertions, properties and sequences (including the Annex F temporal
semantics), checkers, covergroups and crosses, clocking blocks, interfaces,
class inheritance and member resolution, and DPI import/export. These checks
are spread across many translation units but feed the same RTLIR.

The RTLIR consists of `RtlirModule` nodes containing ports, nets, variables,
continuous assignments, net aliases, processes, parameter declarations,
child module instances, function declarations, `let` declarations, sequence
declarations, package imports, class declarations, module attributes, and enum
type maps. Each process carries its sensitivity list and a pointer to its AST
body statement. An `RtlirDesign` collects the top-level modules and a lookup
map of all elaborated modules, along with packages, compilation-unit-scope
function, `let`, and class declarations, a type-width table, and elaboration
diagnostic state (including a simulation-blocked flag set by `$fatal`/`$error`).

## Back End

### Simulator

The Simulator takes the RTLIR produced by the Elaborator and executes the
design over time. The Lowerer translates each RTLIR element into a runtime
object, the SimContext holds all of that state, and the Scheduler drives the
event loop that advances simulation time.

```text
     ┌───────────┐
     │  Lowerer  │
     └─────┬─────┘
           │
           ▼
     ┌───────────┐
     │ Scheduler │◄────┐
     └─────┬─────┘     │
           │           │ event
           ▼           │ loop
     ┌───────────┐     │
     │ Evaluator │─────┘
     └───────────┘
```

Figure 2: Simulator processing stages and event loop.

#### Lowerer

The lowerer translates an `RtlirDesign` into runtime simulation objects and
populates the `SimContext` that holds all simulation state. For each RTLIR
variable it creates a `Variable`, initializing its width, signedness, and
kind (four-state, event, string, real). For each RTLIR net it creates a
`Net` with the appropriate resolution function and driver list. For each
RTLIR process it creates either a coroutine `Process` or a
`CompiledProcess` depending on whether the body contains timing controls.
Continuous assignments are lowered into processes scheduled in the Active
region.

The resulting `SimContext` holds the core simulation state: variables, nets,
the scheduler, and the diagnostic engine. It also references the auxiliary
managers it coordinates with — the DPI context, clocking manager, and coverage
database — while the remaining verification subsystems (VPI, which uses a global
context, plus the assertion, SVA, constraint-solving, and specify managers) are
owned alongside it rather than embedded in it. It provides variable lookup by
name, scope management for function and task calls, and value read/write
operations. It also holds type information for structs, enums, and classes so
that the expression evaluator can perform field access and method dispatch at
runtime, and it manages dynamic arrays, associative arrays, and queues.

All values created during lowering use dual-rail aval/bval encoding per the
VPI convention. Values are packed into 64-bit words. A `Logic4Word` holds
one aval/bval pair
with helpers for testing known/zero/one states, and four-value AND, OR, XOR,
and NOT operations are implemented as bitwise functions on the two rails. A
`Logic4Vec` holds a bit width and a pointer to an arena-allocated array of
`Logic4Word` structs, with flags indicating whether the value represents a
real number, a signed quantity, or a string. A `Logic2Vec` provides a
two-state counterpart where the bval rail is absent, used in contexts where
x and z cannot occur. Signals also carry strength information per IEEE
1800-2023: the `Strength` enum covers eight levels from highz through
supply, and a `StrengthVal` packs the drive-zero strength, drive-one
strength, and logic value into a compact bitfield for strength-aware resolution
when multiple drivers contend on a net.

With this value system in place, a `Variable` stores a `Logic4Vec` value, a
previous value for change detection, and an optional forced value for
`force`/`release` semantics. It also holds a pending NBA value that is
committed during the NBA region. A list of watcher callbacks provides the
sensitivity mechanism: when a variable changes, `NotifyWatchers` invokes
each callback. Callbacks that return false are re-registered for the next
change (persistent watchers), while those that return true are consumed
(one-shot semantics). A `Net` adds multi-driver resolution on top of a
`Variable`. Each driver contributes a `Logic4Vec` and a `DriverStrength`
pair, and the `Resolve` method applies the appropriate resolution function
(wire, wand, wor) to produce the final value. Trireg nets support charge
storage: when all drivers are at Z the net retains its previous value at
the configured charge strength, subject to decay over time.

#### Scheduler

The scheduler implements the IEEE 1800-2023 stratified event algorithm,
dividing each simulation timestep into 17 ordered regions. Events are
stored in a calendar keyed by `SimTime`, with each time slot
holding one event queue per region. Within a timestep the scheduler drains
each region in order, iterating the active and reactive sets until they
stabilize before advancing. Events are allocated from an `EventPool` backed
by an arena allocator and recycled through a free-list to avoid per-event
allocation overhead. Each event carries a callback and an intrusive
next-pointer for queue linkage.

The scheduler drives two kinds of processes. Those that contain timing
controls (`#delay`, `@(posedge clk)`, `wait`) run as C++23 coroutines: the
`SimCoroutine` type wraps a `coroutine_handle` with RAII lifetime management,
and each `co_await` suspends the coroutine and schedules a resume event in
the appropriate region. Processes without timing controls are compiled into
`std::function` lambdas by the `ProcessCompiler`, producing a
`CompiledProcess` whose `Execute` method runs the lambda directly, bypassing
the coroutine machinery. Each `Process` tracks its kind (initial, always,
always_comb, always_latch, always_ff, final, or continuous assignment), its
home region, and whether it belongs to the reactive set.

Beyond basic process scheduling, the `ClockingManager` implements IEEE
clocking block semantics. Each clocking block names a clock signal and edge,
default input and output skews, and a list of member signals with optional
per-signal skew overrides. On a clock edge the manager samples input signals,
stores their values, and schedules output drives with skew delays as
NBA-region events. The VCD writer hooks into the scheduler as a
post-timestep callback, recording signal changes in Value Change Dump
format by assigning a short identifier character to each registered signal
and flushing changed values after each time advance.

Timing constraints are managed by `SpecifyManager`, which handles IEEE
specify block semantics from sections 30 through 32. It stores path delays
(parallel and full, with edge qualifiers and up to twelve transition
delays), timing checks (setup, hold, setuphold, recrem), and SDF
annotations. The SDF parser reads Standard Delay Format files and annotates
the design with backannotated timing data, and runtime queries check for
setup and hold violations given signal transition times.

#### Evaluator

The evaluator interprets AST expression and statement nodes at runtime when
the scheduler dispatches a process. Expression evaluation is split across
several translation units by domain: general expressions, bit and part
select, streaming operators (pack/unpack), array method dispatch (size,
insert, delete, push, pop), enum method dispatch (name, first, last, next,
prev), string method dispatch (substr, toupper, tolower, len), math system
calls, format string processing for $display and $sformatf, and function/task
call evaluation with scope management. System tasks are themselves split by
group: general I/O and file I/O ($fopen, $fclose, $fwrite, $fscanf), array
query, memory load/store ($readmem/$writemem), PLA modeling, and
stochastic/verification tasks. Statement execution
handles blocking, non-blocking, continuous, and force/release assignment
semantics, with a `StmtResult` signaling the control flow outcome of each
statement (normal, break, continue, return, disable).

Two optimization layers sit on top of the base evaluator. The
`ProcessCompiler` identifies pure combinational processes without timing
controls and compiles them into `std::function<void(SimContext&)>` lambdas,
producing a `CompiledProcess` that bypasses the coroutine machinery. The
`Partitioner` then performs dependency analysis on these compiled processes,
grouping non-conflicting ones (those that share no written signals) into
partitions that the `MtScheduler` executes in parallel using `std::jthread`.

Two external interfaces allow code outside SystemVerilog to interact with
the running simulation. The Verilog Procedural Interface (VPI) exposes
simulation objects to C code through the standard `vpi_*` function set.
`VpiContext` builds an object map of modules, ports, nets, variables, and
parameters, supporting handle lookup, object iteration with
`vpi_iterate`/`vpi_scan`, value get/put in multiple formats, and callbacks
for value changes and synchronization events. The Direct Programming
Interface (DPI-C) allows SystemVerilog to call C functions and vice versa.
`DpiContext` maintains registries for imports and exports with argument
descriptors for cross-language value marshaling, and `DpiRuntime` provides
the `svdpi.h` access functions and scope management calls.

The evaluator also drives several verification subsystems. Concurrent
assertions are handled in two layers: the `AssertionMonitor` evaluates
simple SVA-style properties (rose, fell, stable, changed, past) by
registering watchers on monitored signals each cycle, while the `SvaEngine`
handles the full concurrent assertion model with sequence matching, delay,
repetition operators, implication, and disable-iff guards. Deferred
assertions are queued and flushed in the Observed region. Functional
coverage is implemented by `CoverageDB`, where covergroups contain
coverpoints with bins (explicit value sets, auto-generated ranges,
transitions, wildcards, illegal, or ignore) and cross-coverage definitions
over their Cartesian products. The `ConstraintSolver` implements IEEE
randomization with rand and randc qualifiers, supporting range,
set-membership, implication, distribution, and soft constraints through BFS
domain reduction with backtracking.

Additional runtime support includes the UDP evaluator for user-defined
primitive tables, a switch network that resolves bidirectional switch
(tran/tranif) connections, `ClassObject` for SystemVerilog class instance
storage with virtual method dispatch via `SvCallable`, and `SyncObjects` for
simulation-level semaphores and events. A two-state fast-path detector
identifies variables that have never held x or z values for simplified
evaluation, and an event coalescer merges multiple pending updates to the
same target within a region into a single write.

### Synthesizer

The Synthesizer takes the RTLIR produced by the Elaborator and converts it
into a hardware netlist. The SynthLower translates the design into an
And-Inverter Graph, optimization passes reduce its size and depth, and
technology mapping produces the final netlist.

```text
  ┌───────────────┐
  │ Synth Lowerer │
  └───────┬───────┘
          │
          ▼
    ┌───────────┐
    │ Optimizer │
    └─────┬─────┘
          │
          ▼
     ┌─────────┐
     │ Mapper  │
     └────┬────┘
          │
          ▼
     ┌─────────┐
     │ Writer  │
     └─────────┘
```

Figure 3: Synthesizer processing stages from RTLIR to netlist.

#### Synth Lowerer

The synthesis lowerer converts an `RtlirModule` into an And-Inverter Graph
(AIG). It first validates synthesizability, rejecting constructs that have
no hardware equivalent such as system task calls and timing controls. A
standalone memory inference pass exists that analyzes `always_ff` blocks for
array access patterns and describes dedicated memory primitives — recording
each memory's depth, data width, and read/write port configuration — but it is
not yet integrated into `SynthLower::Lower`; it is currently exercised only by
unit tests, and the main flow lowers `always_ff` blocks to latches.

The design is lowered into the AIG as follows. Input
and output ports become AIG primary inputs and outputs. Continuous
assignments and combinational process bodies are lowered expression by
expression, bit by bit, into AND and NOT nodes. `always_ff` blocks produce
latches, and if/case statements are lowered through MUX construction where
each branch contributes signal bits multiplexed by the condition.

The AIG itself is the core synthesis data structure. Each node represents a
two-input AND gate, and edges carry a complement flag in the least
significant bit of the literal encoding so that a literal encodes both node
identity and optional inversion in a single integer. The graph supports AND,
OR (via De Morgan), XOR, and MUX construction. Latches represent sequential
state by pairing a current-state primary input with a next-state literal.
Structural hashing ensures that duplicate AND nodes are never created: a
hash table maps each (fanin0, fanin1) pair to an existing node when one has
already been allocated.

#### Optimizer

Optimization on the AIG is built on two core transforms — constant
propagation, which replaces nodes that are provably constant, and balancing,
which restructures AND trees to minimize critical-path depth. Three further
entry points are layered on top: rewriting (local subgraph replacement using
cut enumeration to reduce node count), refactoring (larger-scope restructuring
for area reduction), and redundancy removal (eliminating stuck-at-fault
redundant nodes). In the current implementation these higher-level passes
delegate substantially to the constant-propagation and balancing core rather
than implementing fully independent algorithms.

#### Mapper

The mapper converts the optimized AIG into target-specific structures
through two complementary flows. LUT mapping partitions the graph into
K-input lookup tables: the `LutMapper` enumerates priority cuts for each
node, selects an area-oriented covering, and produces `LutCell` entries
whose truth tables fit in a 64-bit word for K up to 6 (default K is 4).
Cell mapping instead matches AIG subgraphs against standard cells from a
Liberty timing library. The `Liberty` parser extracts cell definitions
including pin names, directions, Boolean functions, timing arcs, and area
values, and the `CellMapper` produces a `CellMapping` of `CellInstance`
entries naming a library cell and its input and output net connections.
Advanced passes provide delay-oriented LUT mapping that minimizes
critical-path depth, iterative area-delay tradeoff optimization, and forward
register retiming. (Backward retiming is present as a placeholder but does not
yet move registers.)

#### Writer

The netlist writer serializes the AIG into one of four output formats: BLIF
(Berkeley Logic Interchange Format), gate-level Verilog, JSON (nextpnr
interchange), or EDIF. Since AIG nodes do not carry port names, generic names
are synthesized: inputs are named i0, i1, and so on; outputs are named o0,
o1, and so on; internal nodes use the prefix n followed by the node identifier.

## Appendices

### Appendix A: Design Decisions

The lexer and parser are written by hand rather than generated by tools like
flex, bison, or ANTLR. This gives full control over error recovery and
diagnostic quality, and allows the parser to be split across translation units
by grammar domain without the constraints of a generated grammar file.

Each compilation phase uses its own arena allocator. AST nodes live in one
arena and RTLIR nodes in another, so that all memory from a phase can be
reclaimed in a single deallocation rather than requiring per-object cleanup.
Simulation events are recycled through a free-list within the event pool.

C++23 coroutines model `always` blocks naturally: each `co_await` maps to a
timing control. The scheduler resumes coroutines by scheduling events, so the
process suspension and resume mechanism is the same as the event dispatch
mechanism. Processes without timing controls bypass the coroutine machinery
entirely by compiling to plain lambdas.

The aval/bval dual-rail representation matches the VPI standard encoding.
This means VPI get/put operations require no value conversion, and four-value
arithmetic maps to bitwise operations on the two rails.

The project has no external dependencies beyond the C++ standard library. All
components including the lexer, parser, constraint solver, Liberty parser, SDF
parser, AIG optimizer, and technology mapper are implemented from scratch.

### Appendix B: Abbreviations

| Abbreviation | Expansion |
| --- | --- |
| AIG | And-Inverter Graph |
| API | Application Programming Interface |
| AST | Abstract Syntax Tree |
| BFS | Breadth-First Search |
| BLIF | Berkeley Logic Interchange Format |
| DPI | Direct Programming Interface |
| DPI-C | Direct Programming Interface for C |
| EDIF | Electronic Design Interchange Format |
| FSM | Finite State Machine |
| IEEE | Institute of Electrical and Electronics Engineers |
| JSON | JavaScript Object Notation |
| LUT | Look-Up Table |
| MUX | Multiplexer |
| NBA | Non-Blocking Assignment |
| PLA | Programmable Logic Array |
| RAII | Resource Acquisition Is Initialization |
| RTLIR | Register-Transfer Level Intermediate Representation |
| SDF | Standard Delay Format |
| SVA | SystemVerilog Assertion |
| UDP | User-Defined Primitive |
| VCD | Value Change Dump |
| VPI | Verilog Procedural Interface |

### Appendix C: Glossary

arena allocator

> A memory allocation strategy that allocates objects from
> a contiguous block and frees them all at once rather than
> individually.

aval/bval

> The two bit rails in four-value logic encoding. The aval
> rail carries the logic value and the bval rail indicates
> whether the value is known (0) or unknown (1).

backannotation

> The process of applying post-layout timing data, typically
> from an SDF file, back onto a design's timing model.

bin

> A named bucket in a coverpoint that counts how many times
> a particular value or value range has been sampled.

blocking assignment

> An assignment (`=`) that takes effect immediately in the
> current simulation step.

clocking block

> A SystemVerilog construct that groups signals under a
> common clock and specifies input and output skews for
> testbench synchronization.

compiled process

> A process without timing controls that has been translated
> into a direct function call, bypassing coroutine overhead.

constant propagation

> An optimization that replaces signals with their known
> constant values.

continuous assignment

> An `assign` statement that drives a net whenever its
> right-hand side changes.

coroutine

> A C++23 function that can suspend and resume, used to
> model processes with timing controls.

covergroup

> A SystemVerilog construct that defines a set of
> coverpoints and crosses to measure functional coverage.

coverpoint

> A variable or expression monitored for functional
> coverage, with bins that track observed values.

cross-coverage

> Coverage defined over the Cartesian product of two or
> more coverpoints.

cut enumeration

> A technique that identifies all K-input subgraphs (cuts)
> feeding an AIG node, used during technology mapping.

defparam

> A SystemVerilog construct that overrides a parameter value
> at a specific point in the module hierarchy.

driver

> A source that contributes a value to a net. Multiple
> drivers on the same net require resolution.

dual-rail encoding

> A representation using two bit vectors (aval and bval) to
> encode four-value logic states.

elaboration

> The compilation phase that resolves parameters, expands
> generate blocks, evaluates types, and produces the RTLIR.

event coalescing

> Merging multiple pending updates to the same signal within
> a region into a single write.

event pool

> An arena-backed allocator for simulation events that
> recycles used events through a free-list.

force/release

> Simulation commands that override a variable's value
> (force) or restore normal driving (release).

four-value logic

> Logic with four states: 0, 1, x (unknown), and z
> (high-impedance).

free-list

> A linked list of previously allocated and now unused
> objects available for reuse without new allocation.

generate block

> A conditional or loop construct (`if`, `for`, `case`)
> that produces hardware structures at elaboration time
> based on parameter values.

latch

> A level-sensitive storage element in an AIG, pairing a
> current-state input with a next-state literal.

Liberty

> A standard file format (.lib) describing cell timing,
> area, and function for technology mapping.

literal

> In an AIG, an integer encoding both a node identity and
> an optional complement flag in its least significant bit.

lowering

> The translation of an intermediate representation into the
> structures required by a specific back end.

net

> A signal with a resolution function that combines values
> from multiple drivers (e.g., wire, wand, wor).

netlist

> A structural description of a circuit as a list of cells
> and their interconnections.

non-blocking assignment

> An assignment (`<=`) whose new value is scheduled and
> applied in the NBA region rather than immediately.

Pratt parser

> A top-down operator-precedence parsing technique used for
> expression parsing.

primary input

> An AIG node representing an external input to the circuit.

primary output

> An AIG literal representing an external output of the
> circuit.

process

> A simulation execution unit corresponding to an `always`,
> `initial`, or `final` block.

recursive descent

> A top-down parsing technique where each grammar rule is
> implemented as a function.

region

> One of the 17 ordered phases within a simulation
> timestep, as defined by the IEEE stratified event
> algorithm.

resolution function

> A function that combines multiple driver values on a net
> to produce a single resolved value.

retiming

> A synthesis optimization that moves registers across
> combinational logic to improve timing.

sensitivity list

> The set of signals whose changes cause a process to be
> re-evaluated.

specify block

> A SystemVerilog construct that declares path delays and
> timing checks for a module.

structural hashing

> A deduplication technique that ensures identical AIG nodes
> are shared rather than duplicated.

switch network

> The set of bidirectional switch primitives (`tran`,
> `tranif0`, `tranif1`) whose terminals are resolved together
> as a connected node during simulation.

technology mapping

> The process of converting an AIG into cells from a target
> technology library or into LUTs.

timing control

> A statement (`#delay`, `@(event)`, `wait`) that suspends
> a process until a condition is met.

token

> A lexical unit produced by the lexer: a keyword, operator,
> literal, or identifier.

trireg

> A net type that retains its value through charge storage
> when all drivers are at high-impedance.

truth table

> A compact representation of a LUT's Boolean function,
> stored as a 64-bit word for K up to 6.

two-state logic

> Logic with only two states (0 and 1), used where x and z
> cannot occur.

variable

> A single-driver simulation storage element that holds a
> four-value logic vector.

watcher

> A callback registered on a variable that fires when the
> variable's value changes.
