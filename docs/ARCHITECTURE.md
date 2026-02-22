# Architecture

1. [Compilation Pipeline](#compilation-pipeline)
   1. [Preprocessor](#preprocessor)
   2. [Lexer](#lexer)
   3. [Parser](#parser)
   4. [Elaborator](#elaborator)
2. [Simulation](#simulation)
   1. [Lowerer](#lowerer)
   2. [SimContext](#simcontext)
   3. [Event Scheduler](#event-scheduler)
   4. [Process Model](#process-model)
   5. [Four-Value Logic](#four-value-logic)
   6. [Signal Strength](#signal-strength)
   7. [Variables and Nets](#variables-and-nets)
   8. [Expression Evaluation](#expression-evaluation)
   9. [VCD Writer](#vcd-writer)
   10. [VPI](#vpi)
   11. [DPI-C](#dpi-c)
   12. [Compiled Simulation](#compiled-simulation)
   13. [Multi-Threaded Simulation](#multi-threaded-simulation)
   14. [Clocking Blocks](#clocking-blocks)
   15. [Concurrent Assertions](#concurrent-assertions)
   16. [Functional Coverage](#functional-coverage)
   17. [Constrained Random Verification](#constrained-random-verification)
   18. [Timing Specification and SDF](#timing-specification-and-sdf)
   19. [User-Defined Primitives](#user-defined-primitives)
   20. [Class Objects](#class-objects)
   21. [Synchronization Objects](#synchronization-objects)
   22. [Advanced Simulation](#advanced-simulation)
3. [Synthesis](#synthesis)
   1. [SynthLower](#synthlower)
   2. [AIG](#aig)
   3. [AIG Optimization](#aig-optimization)
   4. [Memory Inference](#memory-inference)
   5. [Technology Mapping](#technology-mapping)
   6. [Netlist Writer](#netlist-writer)
4. [Design Decisions](#design-decisions)

DeltaHDL compiles SystemVerilog source files through a staged pipeline. Each
stage transforms the design into a progressively lower-level representation
until it reaches either a running simulation or a mapped netlist.

```
                         Source Files (.sv)
                               │
                               ▼
                      ┌────────────────┐
                      │  Preprocessor  │
                      └───────┬────────┘
                              │
                              ▼
                         ┌─────────┐
                         │  Lexer  │
                         └────┬────┘
                              │
                              ▼
                        ┌──────────┐
                        │  Parser  │
                        └─────┬────┘
                              │
                              ▼
                     CompilationUnit (AST)
                              │
                              ▼
                      ┌──────────────┐
                      │  Elaborator  │
                      └──────┬───────┘
                             │
                             ▼
                      RtlirDesign (RTLIR)
                             │
               ┌─────────────┴─────────────┐
               │                           │
               ▼                           ▼
          ┌───────────┐            ┌──────────────┐
          │ Simulator │            │ Synthesizer  │
          └───────────┘            └──────────────┘
```


## Compilation Pipeline

### Preprocessor

The preprocessor handles macro definitions (`+define+`), file inclusion
(`` `include ``), and conditional compilation (`` `ifdef ``/`` `ifndef ``). It
operates on raw source text before tokenization and produces a single
concatenated string for the lexer. Include directories are specified with
`+incdir+`. It also tracks `` `timescale `` directives and
`` `default_nettype `` declarations, propagating them to the parser through
the preprocessed result.

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
literal escape sequences are handled during tokenization.

### Parser

A recursive-descent parser consumes the token stream and builds an abstract
syntax tree (AST). Expressions use a Pratt parser for correct precedence and
associativity. The parser is split across several translation units organized
by grammar domain: top-level declarations (modules, interfaces, programs,
classes, checkers), type and variable declarations, statements, module
instantiation, port lists, assertions, specify blocks, clocking blocks,
generate constructs, verification constructs (randcase, randsequence), and
configuration declarations. A separate unit handles time-literal resolution.

The AST is allocated in an arena so that the entire tree can be freed in one
shot after elaboration. The top-level AST node is a `CompilationUnit`
containing modules, packages, interfaces, programs, and classes.

### Elaborator

The elaborator walks the AST, resolves types, evaluates constant expressions,
and produces a register-transfer level intermediate representation (RTLIR).
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

The RTLIR consists of `RtlirModule` nodes containing ports, nets, variables,
continuous assignments, net aliases, processes, parameter declarations,
module instances, function declarations, class declarations, and enum type
maps. Each process carries its sensitivity list and a pointer to its AST body
statement. An `RtlirDesign` collects the top-level modules and a lookup map
of all elaborated modules.

After elaboration the pipeline branches into either simulation or synthesis.


## Simulation

```
                    RtlirDesign
                         │
                         ▼
                   ┌──────────┐
                   │  Lowerer  │
                   └─────┬─────┘
                         │
                         ▼
  ┌───────┐        ┌───────────┐        ┌─────────┐
  │  VPI  ├───────►│ SimContext │◄───────┤  DPI-C  │
  └───────┘        └─────┬─────┘        └─────────┘
                         │
                         ▼
                   ┌───────────┐
                   │ Scheduler │
                   └─────┬─────┘
                         │
                         ▼
                  Waveforms (.vcd)
```

### Lowerer

The lowerer translates an `RtlirDesign` into runtime simulation objects. For
each RTLIR variable it creates a `Variable` in the `SimContext`, initializing
its width, signedness, and kind (four-state, event, string, real). For each
RTLIR net it creates a `Net` with the appropriate resolution function and
driver list. For each RTLIR process it creates either a coroutine `Process`
or a `CompiledProcess` depending on whether the body contains timing controls.
Continuous assignments are lowered into processes scheduled in the Active
region.

### SimContext

`SimContext` owns the simulation state: variables, nets, the scheduler, the
diagnostic engine, and auxiliary managers for VPI, DPI, clocking, assertions,
SVA, coverage, constraint solving, specify blocks, and SDF annotations. It
provides variable lookup by name, scope management for function and task
calls, and value read/write operations. It holds type information for structs,
enums, and classes so that the expression evaluator can perform field access
and method dispatch at runtime. It also manages dynamic arrays, associative
arrays, and queues.

### Event Scheduler

The scheduler implements the IEEE 1800-2023 stratified event algorithm. Each
simulation timestep is divided into 17 ordered regions.

```
            ┌─────────────┐
            │  Preponed    │
            ├─────────────┤
            │  PreActive   │
            ├─────────────┤
          ┌─┤  Active      │◄─┐
          │ ├─────────────┤   │
          │ │  Inactive    │   │ active
          │ ├─────────────┤   │ iteration
          │ │  PreNBA      │   │ loop
          │ ├─────────────┤   │
          │ │  NBA         │   │
          │ ├─────────────┤   │
          └─┤  PostNBA     │──┘
            ├─────────────┤
            │  PreObserved │
            ├─────────────┤
          ┌─┤  Observed    │◄─┐
          │ ├─────────────┤   │
          │ │  PostObserved│   │ reactive
          │ ├─────────────┤   │ iteration
          │ │  Reactive    │   │ loop
          │ ├─────────────┤   │
          │ │  ReInactive  │   │
          │ ├─────────────┤   │
          │ │  PreReNBA    │   │
          │ ├─────────────┤   │
          │ │  ReNBA       │   │
          │ ├─────────────┤   │
          └─┤  PostReNBA   │──┘
            ├─────────────┤
            │ PrePostponed │
            ├─────────────┤
            │  Postponed   │
            └─────────────┘
```

Events are stored in a calendar keyed by `SimTime`. Each time slot holds one
event queue per region. Within a timestep the scheduler drains each region in
order, iterating the active and reactive sets until they stabilize before
advancing to the next timestep.

Events are allocated from an `EventPool` backed by an arena allocator. Used
events are recycled through a free-list to avoid per-event allocation
overhead. Each event carries a callback and an intrusive next-pointer for
queue linkage.

### Process Model

Processes that contain timing controls (`#delay`, `@(posedge clk)`, `wait`)
run as C++23 coroutines. The `SimCoroutine` type wraps a `coroutine_handle`
with RAII lifetime management. Each `co_await` suspends the coroutine and
schedules a resume event in the appropriate region. Processes without timing
controls are compiled into `std::function` lambdas by the `ProcessCompiler`,
which walks the AST body and produces a `CompiledProcess` whose `Execute`
method runs the compiled lambda directly, bypassing the coroutine machinery.

Each `Process` tracks its kind (initial, always, always_comb, always_latch,
always_ff, final, or continuous assignment), its home region, and whether
it belongs to the reactive set.

### Four-Value Logic

All simulation values use dual-rail aval/bval encoding per the VPI convention.

```
  ┌───────┬──────┬──────┐
  │ Value │ aval │ bval │
  ├───────┼──────┼──────┤
  │   0   │   0  │   0  │
  │   1   │   1  │   0  │
  │   x   │   0  │   1  │
  │   z   │   1  │   1  │
  └───────┴──────┴──────┘
```

Values are packed into 64-bit words. A `Logic4Word` holds one aval/bval pair
and provides helpers for testing known/zero/one states. Four-value AND, OR,
XOR, and NOT operations are implemented as bitwise functions on the two rails.
A `Logic4Vec` holds a bit width and a pointer to an arena-allocated array of
`Logic4Word` structs, with flags indicating whether the value represents a
real number, a signed quantity, or a string.

A `Logic2Vec` provides a two-state (bit/int/byte) counterpart where the bval
rail is absent, used in contexts where x and z values cannot occur.

### Signal Strength

Signals carry strength information per IEEE 1800-2023. The `Strength` enum
covers all eight levels from highz through supply. A `StrengthVal` packs the
drive-zero strength, drive-one strength, and logic value into a single byte.
Strength-aware resolution is used when multiple drivers contend on a net.

### Variables and Nets

A `Variable` stores a `Logic4Vec` value, a previous value for change
detection, and an optional forced value for `force`/`release` semantics. It
also holds a pending NBA value that is committed during the NBA region. A
list of watcher callbacks provides the sensitivity mechanism: when a variable
changes, `NotifyWatchers` moves the callback list, clears it, and invokes
each callback. Callbacks that return false are re-registered for the next
change (persistent watchers), while those that return true are consumed
(one-shot semantics).

A `Net` adds multi-driver resolution on top of a `Variable`. Each driver
contributes a `Logic4Vec` value and a `DriverStrength` pair. The `Resolve`
method applies the appropriate resolution function (wire, wand, wor) to
produce the final value. Trireg nets support charge storage: when all drivers
are at Z the net retains its previous value at the configured charge strength,
subject to decay over time. Charge propagation between connected trireg nets
is also supported.

### Expression Evaluation

The expression evaluator interprets AST expression nodes at runtime. It is
split across several translation units by domain: general expression
evaluation, array method dispatch (size, insert, delete, push, pop), enum
method dispatch (name, first, last, next, prev), string method dispatch
(substr, toupper, tolower, len), math system calls, file I/O system calls
($fopen, $fclose, $fwrite, $fscanf), format string processing for $display
and $sformatf, and function/task call evaluation with scope management.

Statement execution is similarly split into general statement dispatch, and
assignment evaluation which handles blocking, non-blocking, continuous, and
force/release assignment semantics. A `StmtResult` signals the control flow
outcome of each statement (normal, break, continue, return, disable).

### VCD Writer

The VCD writer records signal changes during simulation and writes them in
Value Change Dump format per IEEE 1800-2023. It assigns a short identifier
character to each registered signal. The scheduler invokes it as a
post-timestep callback so that changed values are flushed after each time
advance.

### VPI

The Verilog Procedural Interface exposes simulation objects to external C code
through the standard `vpi_*` function set defined in IEEE 1800-2023 sections
36 through 39. `VpiContext` attaches to a `SimContext` and builds an object
map of modules, ports, nets, variables, and parameters. It supports handle
lookup by name and index, object iteration with `vpi_iterate`/`vpi_scan`,
value get/put in multiple formats (binary string, hex string, scalar, integer,
real, vector), and callbacks for value changes, read-write synchronization,
and end-of-simulation events. The C API type aliases and constant macros
follow the IEEE-mandated naming conventions.

### DPI-C

The Direct Programming Interface allows SystemVerilog code to call C functions
(imports) and C code to call SystemVerilog functions (exports). `DpiContext`
maintains separate registries for imports and exports, mapping SystemVerilog
names to C function names. Each import carries argument descriptors with
type and direction information so that the expression evaluator can marshal
values across the language boundary.

A separate `DpiRuntime` module provides the `svdpi.h` access functions
(`svGetBitselBit`, `svGetPartselLogic`, `svPutPartselLogic`, and related
routines) as well as scope and context management calls required by the
IEEE standard.

### Compiled Simulation

The `ProcessCompiler` analyzes process bodies to determine whether they are
eligible for compilation. Only pure combinational processes without timing
controls qualify. For those that do, it produces a `CompiledProcess` wrapping
a `std::function<void(SimContext&)>` lambda. The lambda evaluates the process
body directly, avoiding the overhead of coroutine creation and suspension.

### Multi-Threaded Simulation

The `Partitioner` performs dependency analysis on compiled processes by
examining which signals each process reads and writes. It groups
non-conflicting processes (those that share no written signals) into
partitions. The `MtScheduler` executes independent partitions in parallel
using `std::jthread`, while partitions that conflict with one another run
sequentially within the same thread.

### Clocking Blocks

`ClockingManager` implements IEEE clocking block semantics. Each clocking
block names a clock signal and edge, default input and output skews, and a
list of member signals with optional per-signal skew overrides. On a clock
edge the manager samples input signals and stores their values. Output drives
are scheduled with skew delays as NBA-region events. Default and global
clocking blocks are tracked. Each block can have an associated named-event
variable that is triggered on its clock edge, and user callbacks can be
registered to fire on those edges.

### Concurrent Assertions

Two layers implement SystemVerilog assertion semantics. The
`AssertionMonitor` evaluates simple SVA-style properties (rose, fell, stable,
changed, past, and custom predicates) by registering watchers on monitored
signals and checking them each cycle. It tracks per-property pass and fail
counts.

The `SvaEngine` handles the full concurrent assertion model described in
section 16. It supports sequence matching with delay, consecutive repetition,
goto repetition, and non-consecutive repetition operators. Sequence-level
AND, OR, intersect, and throughout operators compose sequences. Property
evaluation covers overlapping and non-overlapping implication, property
negation, conjunction, disjunction, and disable-iff guards. Deferred
assertions are queued and flushed in the Observed region. Per-instance
assertion control (enable, disable, kill, pass-off, fail-off) is managed
by `AssertionControl`.

### Functional Coverage

`CoverageDB` implements the IEEE functional coverage model from section 19.
Covergroups contain coverpoints and cross-coverage definitions. Coverpoints
hold bins which may be explicit value sets, automatically generated ranges,
transition sequences, wildcard patterns, illegal bins, or ignore bins. Each
bin tracks its hit count against an at-least threshold. Cross-coverage
generates product bins across multiple coverpoints. The `Sample` method
updates bin counts given a set of named values, and coverage percentage
queries are available at the coverpoint, cross, covergroup, and global
levels.

### Constrained Random Verification

The `ConstraintSolver` implements the IEEE randomization model from section
18. It supports rand and randc variable qualifiers, with randc variables
maintaining a cyclic history to avoid repeats. Constraint blocks may contain
range, set-membership, equality, relational, implication, foreach, unique,
distribution, soft, and custom-evaluator constraints. The solver uses
BFS domain reduction with backtracking. Inline constraints via `randomize()
with` are supported. Per-variable `rand_mode` and per-block
`constraint_mode` controls are available. Pre-randomize and post-randomize
callbacks are invoked around each solve.

### Timing Specification and SDF

`SpecifyManager` handles IEEE specify block semantics from sections 30
through 32. It stores path delays (parallel and full, with edge
qualifiers and up to twelve transition delays), timing checks (setup, hold,
setuphold, recrem, and others with reference and data edges), and SDF
annotations. Runtime queries check for setup and hold violations given
signal transition times.

The SDF parser reads Standard Delay Format files and annotates the design
with backannotated timing data.

### User-Defined Primitives

The UDP evaluator executes user-defined primitive tables at simulation time,
supporting both combinational and sequential primitive semantics as defined
in section 29.

### Class Objects

`ClassObject` provides runtime storage for SystemVerilog class instances.
The simulation context tracks class type information and allocates object
handles for `new` expressions. Properties are accessed by name through the
expression evaluator. The `SvCallable` module supports SystemVerilog
subroutine dispatch including virtual methods and interface class calls.

### Synchronization Objects

Simulation-level synchronization primitives (semaphores and events) are
provided through `SyncObjects`, supporting the inter-process communication
patterns described in the IEEE standard.

### Advanced Simulation

Several auxiliary simulation utilities reside in the advanced simulation
module. A two-state fast-path detector identifies variables that have never
held x or z values and can use simplified evaluation. An event coalescer
merges multiple pending updates to the same target within a region into a
single write. Runtime representations for dynamic arrays, associative arrays,
and SystemVerilog strings are also provided here.


## Synthesis

```
                    RtlirDesign
                         │
                         ▼
                   ┌─────────────┐
                   │  SynthLower  │
                   └──────┬───────┘
                          │
                          ▼
                   ┌─────────────┐
                   │   AIG Opts   │
                   └──────┬───────┘
                          │
                          ▼
              ┌───────────┴───────────┐
              │                       │
              ▼                       ▼
         ┌──────────┐          ┌───────────┐
         │ LUT Map  │          │ Cell Map  │
         └─────┬────┘          └─────┬─────┘
               │                     │
               └──────────┬──────────┘
                          │
                          ▼
              Netlist (.blif, .v, .json)
```

### SynthLower

The synthesis lowerer converts an `RtlirModule` into an And-Inverter Graph
(AIG). It first validates synthesizability, rejecting constructs that have no
hardware equivalent such as system task calls and timing controls. Input and
output ports are mapped to AIG primary inputs and outputs. Continuous
assignments and combinational process bodies are lowered expression by
expression, bit by bit, into AND and NOT nodes. `always_ff` blocks produce
latches in the AIG. `always_latch` blocks are lowered similarly. If and case
statements are lowered through MUX construction, where each branch contributes
a set of signal bits that are multiplexed by the condition.

### AIG

The And-Inverter Graph is the core synthesis data structure. Each node
represents a two-input AND gate. Edges carry a complement flag in the least
significant bit of the literal encoding, so a literal encodes both the node
identity and an optional inversion in a single integer. Constant-false is
literal 0, constant-true is literal 1. The graph supports construction of
AND, OR (via De Morgan), XOR, and MUX nodes. Latches represent sequential
state: each latch pairs a current-state primary input with a next-state
literal. Structural hashing ensures that duplicate AND nodes are never created;
a hash table maps each (fanin0, fanin1) pair to an existing node when one has
already been allocated.

### AIG Optimization

Five optimization passes operate on the AIG. Constant propagation replaces
outputs that are provably constant. Balancing restructures AND trees to
minimize critical-path depth. Rewriting applies local subgraph replacement
using cut enumeration to reduce node count. Refactoring performs
larger-scope restructuring for area reduction. Redundancy removal identifies
and eliminates stuck-at-fault redundant nodes.

### Memory Inference

The memory inference pass analyzes `always_ff` blocks in the RTLIR for
array access patterns (indexed reads and writes) and replaces them with
dedicated memory primitives before AIG lowering. Each inferred memory
records its depth, data width, and a set of read and write ports with
address width, data width, and clock edge information.

### Technology Mapping

LUT mapping partitions the AIG into K-input lookup tables. The `LutMapper`
enumerates priority cuts for each AIG node and selects an area-oriented
covering to produce `LutCell` entries for every output. Each LUT cell stores
its input node identifiers and a truth table that fits in a 64-bit word for
K up to 6. The default LUT size is 4.

Cell mapping matches AIG subgraphs against standard cells from a Liberty
timing library. The `Liberty` parser extracts cell definitions including
pin names, directions, Boolean functions, timing arcs, and area values. The
`CellMapper` produces a `CellMapping` of `CellInstance` entries, each naming
a library cell and its input and output net connections.

Advanced synthesis passes provide delay-oriented LUT mapping that minimizes
critical-path depth, iterative area-delay tradeoff optimization, and register
retiming in both forward and backward directions.

### Netlist Writer

The netlist writer serializes the AIG into one of four output formats: BLIF
(Berkeley Logic Interchange Format), gate-level Verilog, JSON (nextpnr
interchange), or EDIF. Since AIG nodes do not carry port names, generic names
are synthesized: inputs are named i0, i1, and so on; outputs are named o0,
o1, and so on; internal nodes use the prefix n followed by the node identifier.


## Design Decisions

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
