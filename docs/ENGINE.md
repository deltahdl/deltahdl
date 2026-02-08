# DeltaHDL Engine Architecture

DeltaHDL is a from-scratch SystemVerilog IEEE 1800-2023 event-driven simulator and
logic synthesizer written in C++23. This document defines the architecture of its
core engine.

## 1. Compilation Pipeline

Source files flow through a shared frontend, then fork into simulation or
synthesis paths after elaboration. Each stage has a clean interface boundary
so it can be tested and developed independently.

```
 .sv files
    │
    ▼
┌──────────────┐
│ Preprocessor │  `define, `include, `ifdef, `timescale, ...
└──────┬───────┘
       │  character stream (expanded)
       ▼
┌──────────────┐
│    Lexer     │  Tokens: keywords, identifiers, literals, operators
└──────┬───────┘
       │  token stream
       ▼
┌──────────────┐
│    Parser    │  Recursive-descent + Pratt expression parsing
└──────┬───────┘
       │  AST (arena-allocated)
       ▼
┌──────────────┐
│ Elaboration  │  Hierarchy binding, parameter resolution, generate expansion
└──────┬───────┘
       │  Elaborated design model (RTLIR)
       │
       ├──────────────────────────────────┐
       ▼                                  ▼
┌──────────────┐                   ┌──────────────┐
│ Sim Lowering │                   │ Synth Lower  │  RTLIR → logic network
└──────┬───────┘                   └──────┬───────┘
       │                                  │  AIG/MIG netlist
       ▼                                  ▼
┌──────────────┐                   ┌──────────────┐
│  Simulation  │                   │  Synthesis   │  Optimize → tech map → output
└──────────────┘                   └──────────────┘
```

### 1.1 Preprocessor

Handles all 23 compiler directives (IEEE 1800-2023 §22):

| Directive | Purpose |
|-----------|---------|
| `` `define ``, `` `undef ``, `` `undefineall `` | Text macro definition and expansion |
| `` `include `` | File inclusion (≥15 nesting levels) |
| `` `ifdef ``, `` `ifndef ``, `` `elsif ``, `` `else ``, `` `endif `` | Conditional compilation |
| `` `timescale `` | Default time unit/precision |
| `` `default_nettype `` | Implicit net type |
| `` `resetall `` | Reset all directives |
| `` `celldefine ``, `` `endcelldefine `` | Cell module marking |
| `` `unconnected_drive ``, `` `nounconnected_drive `` | Unconnected port handling |
| `` `pragma `` | Implementation pragmas |
| `` `line `` | Source location override |
| `` `__FILE__ ``, `` `__LINE__ `` | Predefined text macros |
| `` `begin_keywords ``, `` `end_keywords `` | Keyword version control |

Output: a character stream with all directives resolved, retaining source location
mappings for diagnostics.

### 1.2 Lexer

Hand-written lexer (no lex/flex dependency). Produces tokens for:
- ~260 reserved keywords (Annex B)
- Identifiers (simple and escaped `\...whitespace`)
- Integer literals (decimal, hex `'h`, octal `'o`, binary `'b`, sized/unsized, signed/unsigned)
- Real literals (fixed-point and exponential)
- Time literals (`100ns`, `1.5ps`, etc.)
- String literals (with special characters)
- Operators and punctuation
- System identifiers (`$display`, `$finish`, etc.)

Each token carries a `SourceLoc` (file ID, line, column) for diagnostics.

### 1.3 Parser

Hand-written recursive-descent parser implementing the Annex A BNF grammar.
Expressions use Pratt (top-down operator precedence) parsing for correct
precedence and associativity per §11 Table 11-2.

Produces an arena-allocated AST. No external parser generator (no bison/ANTLR)
for better error messages, IDE integration, and incremental parsing potential.

Key AST node categories:
- **Source text**: `ModuleDecl`, `InterfaceDecl`, `ProgramDecl`, `PackageDecl`, `ClassDecl`
- **Declarations**: `NetDecl`, `VarDecl`, `ParamDecl`, `TypedefDecl`, `PortDecl`
- **Statements**: `BlockStmt`, `IfStmt`, `CaseStmt`, `ForStmt`, `WhileStmt`, `ForkStmt`
- **Expressions**: `BinaryExpr`, `UnaryExpr`, `TernaryExpr`, `CallExpr`, `SelectExpr`
- **Processes**: `InitialBlock`, `AlwaysBlock`, `AlwaysCombBlock`, `AlwaysFFBlock`, `FinalBlock`
- **Assignments**: `ContAssign`, `BlockingAssign`, `NonblockingAssign`

### 1.4 Elaboration

Transforms the AST into an elaborated design model (RTLIR):

1. **Top-level resolution** — identify top module(s) from command line
2. **Recursive instantiation** — walk hierarchy, instantiate each module/interface/program
3. **Parameter evaluation** — resolve parameter overrides (`#(...)` and `defparam`)
4. **Generate expansion** — evaluate `generate for`/`generate if`/`generate case` at elaboration time
5. **Port binding** — connect ports via implicit continuous assignments or bidirectional connections (§4.9.6)
6. **Type resolution** — resolve typedefs, packed dimensions, implicit types
7. **Sensitivity inference** — compute sensitivity lists for `always_comb`/`always_latch` blocks (§9.2.2)

### 1.5 Simulation Lowering

Translates RTLIR into executable simulation objects:
- Each `always`/`initial`/`final` block → a `Process` (coroutine)
- Each continuous assignment → a `ContAssignProcess` sensitive to its RHS signals
- Each net → a `Net` object with driver list and resolution function
- Each variable → a `Variable` object with storage
- Sensitivity edges → entries in the scheduler's sensitivity map

### 1.6 Simulation

The stratified event scheduler (§4.4–4.5). Described in detail in §3 below.

### 1.7 Synthesis Lowering

Translates the synthesizable subset of RTLIR into a logic network:

1. **Synthesizability check** — reject unsynthesizable constructs (delays, `initial`
   blocks, system tasks, dynamic types, classes) with clear diagnostics
2. **Process flattening** — convert `always_comb` → combinational logic cones,
   `always_ff` → register + next-state logic, `always_latch` → latch + enable logic
3. **Logic network construction** — build an And-Inverter Graph (AIG) or
   Majority-Inverter Graph (MIG) from the flattened logic
4. **Memory inference** — detect RAM/ROM patterns from array assignments

### 1.8 Synthesis

Logic optimization and technology mapping. Described in detail in §13 below.

## 2. Core Data Structures

### 2.1 Four-Value Logic Representation

SystemVerilog has a 4-value logic system: `0`, `1`, `x`, `z` (§6.3).

**Encoding**: dual-rail bit-pair per the VPI convention. Each logic bit is encoded
in two physical bits across two words (`aval`, `bval`):

| Logic value | aval | bval |
|:-----------:|:----:|:----:|
| `0`         | 0    | 0    |
| `1`         | 1    | 0    |
| `x`         | 0    | 1    |
| `z`         | 1    | 1    |

This encoding enables bulk bitwise operations on 64-bit words:

```cpp
struct Logic4Word {
    uint64_t aval;  // value bits
    uint64_t bval;  // unknown/highz marker bits

    // If bval == 0, all bits are known (0 or 1)
    bool is_known() const { return bval == 0; }
};
```

A vector of arbitrary width:

```cpp
struct Logic4Vec {
    uint32_t width;             // bit width
    uint32_t nwords;            // ceil(width / 64)
    Logic4Word* words;          // arena-allocated, LSB-first

    // Fast path: for width ≤ 64, inline single word (no pointer chase)
};
```

**2-state optimization**: `bit`, `int`, `byte`, `shortint`, `longint` types use
`Logic2Vec` (single `uint64_t*` array, half the memory, no `bval` overhead).

### 2.2 Signal Strength

Strengths apply to nets only (§6.3.2, §28.11). Each bit of a driven net carries
a strength pair `(strength0, strength1)` on a 0–7 scale:

```
supply(7) > strong(6) > pull(5) > large(4) > weak(3) > medium(2) > small(1) > highz(0)
```

```cpp
struct StrengthVal {
    uint8_t s0 : 4;  // strength toward 0
    uint8_t s1 : 4;  // strength toward 1
    uint8_t val : 2; // resolved logic value (0, 1, x, z)
};
```

Most nets use default `(strong0, strong1)` strengths. The strength model is only
allocated for nets that actually participate in multi-driver resolution or have
explicit strength specifications.

### 2.3 Simulation Time

```cpp
struct SimTime {
    uint64_t ticks;  // time in units of the global time precision (smallest timeprecision)

    // Comparison operators for time-ordered scheduling
};
```

### 2.4 Event Queue

The time-ordered event queue is the central scheduler data structure:

```cpp
enum class Region : uint8_t {
    Preponed, PreActive, Active, Inactive,
    PreNBA, NBA, PostNBA,
    PreObserved, Observed, PostObserved,
    Reactive, ReInactive,
    PreReNBA, ReNBA, PostReNBA,
    PrePostponed, Postponed,
    COUNT  // = 17
};

struct TimeSlot {
    std::array<EventQueue, 17> regions;
    bool any_nonempty() const;
    bool any_nonempty_in(Region first, Region last) const;
};

// Top-level: time → time slot
std::map<SimTime, TimeSlot> event_calendar;
```

Each `EventQueue` is an intrusive linked list of `Event` objects (update events
and evaluation events) for O(1) insert/remove.

### 2.5 Processes

Each concurrent process (initial, always, continuous assignment, etc.) is a
C++23 coroutine:

```cpp
struct Process {
    enum Kind { Initial, Always, AlwaysComb, AlwaysLatch, AlwaysFF, Final, ContAssign };

    Kind kind;
    ProcessHandle coro;         // coroutine handle
    Region home_region;         // Active for design, Reactive for programs/checkers
    SensitivityList* sens;      // signals this process is sensitive to
};
```

Timing controls (`#delay`, `@(posedge clk)`, `wait(expr)`) are implemented as
coroutine suspend points with custom awaitables:

```cpp
// Example: #10 becomes
co_await delay_awaitable(SimTime{10 * time_scale});

// Example: @(posedge clk) becomes
co_await edge_awaitable(clk_signal, Edge::Posedge);
```

`fork`/`join` spawns child coroutines; `join` suspends until all children complete,
`join_any` until one completes, `join_none` continues immediately.

### 2.6 Nets and Drivers

```cpp
struct Net {
    NetType type;               // wire, tri, wand, wor, tri0, tri1, supply0, supply1, trireg, uwire
    Logic4Vec value;            // current resolved value
    StrengthVal* strengths;     // per-bit strength (null if default-strength single-driver)
    SmallVec<Driver*> drivers;  // list of continuous assignment / port / gate drivers
    ResolutionFn resolve;       // built-in or user-defined resolution function
};

struct Driver {
    Logic4Vec driven_value;
    StrengthVal* strengths;
    Process* source;            // the process driving this net
};
```

When any driver updates, the net's `resolve()` function is called to produce the
new resolved value. Built-in resolution follows the truth tables in §6.6
(wire/tri, wand/triand, wor/trior, tri0, tri1, supply0/supply1, trireg, uwire).

### 2.7 Variables

```cpp
struct Variable {
    Logic4Vec value;            // current value (4-state)
    // OR: Logic2Vec for 2-state types
    bool is_forced;             // under force statement
    Logic4Vec forced_value;     // value while forced
};
```

## 3. Stratified Event Scheduler

The scheduler implements the IEEE 1800-2023 §4.5 reference algorithm exactly.

### 3.1 Algorithm

```
execute_simulation:
    T = 0
    initialize all nets and variables
    schedule initialization events into time-zero slot
    while event_calendar is not empty:
        T = first nonempty time slot
        execute_time_slot(T)

execute_time_slot(T):
    execute_region(Preponed)
    execute_region(PreActive)
    while any region in [Active..PrePostponed] is nonempty:
        // Active region set iteration
        while any region in [Active..PostObserved] is nonempty:
            execute_region(Active)
            R = first nonempty region in [Active..PostObserved]
            if R is nonempty:
                move events from R to Active
        // Reactive region set iteration
        while any region in [Reactive..PostReNBA] is nonempty:
            execute_region(Reactive)
            R = first nonempty region in [Reactive..PostReNBA]
            if R is nonempty:
                move events from R to Reactive
        // Pre-Postponed (only if all iterative regions empty)
        if all regions in [Active..PostReNBA] are empty:
            execute_region(PrePostponed)
    execute_region(Postponed)

execute_region(R):
    while R is nonempty:
        E = take any event from R
        if E is an update event:
            update the target object
            schedule evaluation events for all sensitive processes
        else:  // evaluation event
            resume the process coroutine
            (which may schedule further events)
```

### 3.2 Region Semantics Summary

| Region | Purpose | What schedules here |
|--------|---------|---------------------|
| **Preponed** | Sample before time slot begins | `#1step` sampling, property preponed values |
| **PreActive** | PLI callbacks before Active | `cbAfterDelay`, `cbNextSimTime`, `cbAtStartOfSimTime` |
| **Active** | Main design execution | Blocking assignments, continuous assignment updates, `$display`, process evaluation |
| **Inactive** | `#0` delay events | Explicit `#0` suspends process, reschedules here |
| **PreNBA** | PLI before NBA | `cbNBASynch` |
| **NBA** | Nonblocking assignment updates | `<=` RHS evaluated in Active, LHS updated here |
| **PostNBA** | PLI after NBA | `cbReadWriteSynch` (post) |
| **PreObserved** | PLI read-only after active set stable | Pre-observed PLI callbacks |
| **Observed** | Property/assertion evaluation | Concurrent assertion triggers |
| **PostObserved** | PLI after property eval | Post-observed PLI callbacks |
| **Reactive** | Program/checker execution | `program` block assignments, assertion action blocks |
| **ReInactive** | `#0` in reactive context | Reactive `#0` delays |
| **PreReNBA** | PLI before Re-NBA | Reactive PLI callbacks |
| **ReNBA** | Reactive nonblocking updates | `<=` in program/checker blocks |
| **PostReNBA** | PLI after Re-NBA | Reactive PLI callbacks |
| **PrePostponed** | PLI end-of-timestep | `cbAtEndOfSimTime` |
| **Postponed** | Read-only end of time slot | `$monitor`, `$strobe`, `cbReadOnlySynch` |

### 3.3 Assignment Scheduling Rules

Per §4.9:

| Assignment type | Evaluation | Update scheduled in |
|----------------|------------|---------------------|
| Continuous assignment | When any RHS operand changes | Active (update event) |
| Blocking `=` | Immediate (in-order) | Active (inline) |
| Blocking `= #0` | RHS evaluated, process suspended | Inactive, resumes in next Active iteration |
| Blocking `= #N` | RHS evaluated, process suspended | Active region of time T+N |
| Nonblocking `<=` | RHS evaluated immediately | NBA region of current time |
| Nonblocking `<= #N` | RHS evaluated immediately | NBA region of time T+N |
| `assign` (procedural continuous) | Continuous re-evaluation | Active (like continuous) |
| `force` | Override all drivers | Active (immediate) |

## 4. Process Model

### 4.1 C++23 Coroutines

Each SystemVerilog process maps to a C++23 coroutine. The coroutine type
(`SimCoroutine`) uses a custom promise type that integrates with the scheduler:

- **`co_await delay(N)`** — schedule wakeup event at `T + N`, suspend
- **`co_await edge(signal, posedge/negedge)`** — add to signal's sensitivity list, suspend
- **`co_await wait(expr)`** — if expr is false, add to sensitivity list of expr operands, suspend; re-evaluate on wake
- **`co_await event_trigger(ev)`** — wait for named event
- **`co_return`** — process completes (for `initial`/`final` blocks)

For `always` blocks, the coroutine is wrapped in an implicit infinite loop by the
lowering stage.

### 4.2 Process Initialization (§9.2)

At time zero:
1. All `initial` and `always` processes are scheduled in the Active region
2. All continuous assignments are evaluated and scheduled in the Active region
3. `always_comb` and `always_latch` blocks trigger once automatically at time zero
   (after all `initial`/`always` blocks have started) even without input changes
4. `final` blocks are not scheduled; they execute at `$finish` time

### 4.3 Fork/Join

```systemverilog
fork
    // thread A
    // thread B
join        // wait for ALL to finish
join_any    // wait for ANY to finish
join_none   // don't wait, continue immediately
```

Implementation: `fork` spawns child coroutines. The parent coroutine suspends
(for `join`/`join_any`) or continues (`join_none`). Child completions decrement
a join counter; when the condition is met, the parent is rescheduled.

## 5. Net Resolution Engine

### 5.1 Built-in Resolution Functions (§6.6)

For each net type, a resolution function combines all driver values:

**wire/tri** (default): if drivers agree → that value; if drivers conflict with
equal strength → `x`. Full truth table from §6.6 Table 6-2.

**wand/triand**: wired-AND — result is `0` if ANY driver is `0`.

**wor/trior**: wired-OR — result is `1` if ANY driver is `1`.

**tri0/tri1**: like wire but default pull to `0`/`1` when all drivers are `z`.

**supply0/supply1**: constant `0`/`1` at supply strength.

**trireg**: retains last driven value (capacitive charge) when all drivers go `z`.
Charge decays after specified delay.

**uwire**: error if more than one driver.

### 5.2 Strength Resolution (§28.12)

When multiple drivers have strengths:
1. For each bit, collect all driver `(value, strength0, strength1)` pairs
2. Stronger signal dominates
3. Equal strength + opposing values → `x` at that strength level
4. Range of ambiguous strengths tracked for three-state resolution

### 5.3 User-Defined Nettypes (§6.6.7)

User-defined nettypes specify a `resolution function` with signature:
```systemverilog
function automatic T resolve(input T driver[]);
```
The engine calls this function (as a compiled/interpreted SV function) whenever
any driver of the net changes.

## 6. Memory Management

### 6.1 Arena Allocators

Each compilation phase uses a dedicated arena:
- **Preprocessor arena** — expanded source text, macro tables (freed after lexing)
- **Lexer arena** — token storage (freed after parsing)
- **AST arena** — all AST nodes (lives through elaboration, freed after lowering)
- **RTLIR arena** — elaborated design (freed after lowering)
- **Simulation arena** — simulation objects (lives for entire simulation run)

Arenas provide:
- Bump-pointer allocation (fast, no per-object free)
- Cache-friendly memory layout
- Bulk deallocation at phase boundaries

### 6.2 Object Pools

High-frequency allocations during simulation use object pools:
- **Event pool** — pre-allocated events recycled after execution
- **Driver update pool** — temporary driver value storage

## 7. CLI Interface

```
deltahdl [options] <source-files...>

Options:
  -o <name>              Set simulation output name
  --top <module>         Specify top-level module(s)
  --timescale <t/p>      Override default timescale
  --seed <n>             Random seed for $random, $urandom
  --max-time <time>      Maximum simulation time
  --vcd <file>           Dump waveforms in VCD format
  --fst <file>           Dump waveforms in FST format (compressed)
  +define+<name>=<val>   Command-line `define
  +incdir+<path>         Additional include directories
  -f <file>              Read options from file
  -v <file>              Verilog library file
  -y <dir>               Verilog library directory
  --synth                Synthesize instead of simulate (see §13.7)
  --lint-only            Parse and elaborate only
  --dump-ast             Dump parsed AST (debug)
  --dump-ir              Dump elaborated RTLIR (debug)
  -Wall                  Enable all warnings
  -Werror                Treat warnings as errors
  --version              Print version
  --help                 Print help
```

### 7.1 System Tasks and Functions

Initial set of built-in system tasks/functions:

| Task/Function | Region | Purpose |
|---------------|--------|---------|
| `$display` | Active | Print with newline |
| `$write` | Active | Print without newline |
| `$strobe` | Postponed | Print at end of time step |
| `$monitor` | Postponed | Print on change |
| `$time` | — | Return current simulation time |
| `$realtime` | — | Return current time as real |
| `$finish` | — | End simulation |
| `$stop` | — | Pause simulation |
| `$random` | — | Random integer |
| `$urandom` | — | Unsigned random |
| `$urandom_range` | — | Random in range |
| `$readmemh` | — | Load hex memory file |
| `$readmemb` | — | Load binary memory file |
| `$dumpfile` | — | Set VCD output file |
| `$dumpvars` | — | Enable VCD dumping |
| `$dumpoff`/`$dumpon` | — | Control VCD dumping |
| `$fatal`/`$error`/`$warning`/`$info` | — | Severity system tasks |

### 7.2 Waveform Output

**VCD** (Value Change Dump): IEEE 1800-2023 §21. Text-based, universally supported.

**FST** (Fast Signal Trace): Compressed binary format via GTKWave's libfst. Much
smaller files, faster writing. Optional dependency.

## 8. Source Tree Layout

```
src/
├── main.cpp                    # Entry point, CLI argument parsing
├── common/
│   ├── arena.h                 # Arena allocator
│   ├── types.h                 # Logic4Word, Logic4Vec, Logic2Vec, StrengthVal, SimTime
│   ├── types.cpp               # Logic operations (AND, OR, XOR, etc. on 4-value vecs)
│   ├── source_loc.h            # SourceLoc, source manager
│   └── diagnostic.h/.cpp       # Error/warning reporting
├── preprocessor/
│   ├── preprocessor.h/.cpp     # Directive processing, macro expansion
│   └── macro_table.h/.cpp      # Macro storage and lookup
├── lexer/
│   ├── lexer.h/.cpp            # Tokenization
│   ├── token.h                 # Token types and Token struct
│   └── keywords.h/.cpp         # Keyword table (gperf or minimal perfect hash)
├── parser/
│   ├── parser.h/.cpp           # Recursive-descent parser
│   ├── expr_parser.cpp         # Pratt expression parser
│   └── ast.h                   # AST node definitions
├── elaboration/
│   ├── elaborator.h/.cpp       # Hierarchy expansion, parameter resolution
│   ├── rtlir.h                 # Elaborated design IR nodes
│   ├── type_eval.h/.cpp        # Type resolution and evaluation
│   └── const_eval.h/.cpp       # Constant expression evaluator
├── simulation/
│   ├── scheduler.h/.cpp        # Stratified event scheduler (§4.5 algorithm)
│   ├── process.h/.cpp          # C++23 coroutine process model
│   ├── net.h/.cpp              # Net objects, driver lists, resolution functions
│   ├── variable.h/.cpp         # Variable storage
│   ├── systask.h/.cpp          # Built-in $display, $finish, etc.
│   └── vcd_writer.h/.cpp       # VCD waveform output
├── synthesis/
│   ├── synth_lower.h/.cpp      # RTLIR → AIG synthesis lowering
│   ├── aig.h/.cpp              # And-Inverter Graph data structure
│   ├── aig_rewrite.h/.cpp      # AIG rewriting optimization pass
│   ├── aig_refactor.h/.cpp     # AIG refactoring optimization pass
│   ├── aig_balance.h/.cpp      # AIG balancing optimization pass
│   ├── lut_map.h/.cpp          # FPGA LUT-based technology mapping
│   ├── cell_map.h/.cpp         # ASIC standard-cell technology mapping
│   ├── liberty.h/.cpp          # Liberty (.lib) file parser
│   └── netlist_writer.h/.cpp   # Verilog/BLIF/JSON/EDIF output
└── vpi/
    └── vpi_stub.h/.cpp         # VPI interface stubs (future)

test/
├── unit/                       # Per-module unit tests
│   ├── test_logic4.cpp
│   ├── test_lexer.cpp
│   ├── test_parser.cpp
│   ├── test_scheduler.cpp
│   ├── test_aig.cpp
│   └── ...
└── integration/                # End-to-end simulation tests
    ├── hello.sv                # $display("Hello, DeltaHDL!")
    ├── counter.sv              # Basic sequential logic
    ├── alu.sv                  # Combinational logic
    └── ...
```

## 9. Code Constraints

All C++ source in this project must follow these hard limits:

| Constraint | Limit |
|------------|-------|
| Nesting depth | ≤ 3 levels |
| Arguments per function | ≤ 5 |
| Statements per function | ≤ 50 |
| Lines per file | ≤ 800 |
| Algorithmic complexity | Big-O optimized (prefer O(1)/O(log n) over O(n) where possible) |

These constraints enforce small, focused functions and files. When a function or
file approaches a limit, split it. Prefer composing small functions over deeply
nested logic. Use early returns to flatten control flow. Pass configuration via
structs when argument count would exceed 5.

## 10. Build System

CMake with the following configuration:
- **C++23** standard (for coroutines, `std::expected`, `std::format`)
- **No external dependencies** for the core engine
- Optional: libfst for FST waveform output
- **Testing**: Catch2 or GoogleTest for unit tests
- **Sanitizers**: ASan, UBSan enabled in debug builds

## 11. Conformance Testing

IEEE 1800-2023 conformance is validated using the
[CHIPS Alliance sv-tests](https://github.com/chipsalliance/sv-tests) suite.
This is an open-source collection of SystemVerilog compliance tests that covers
lexing, parsing, elaboration, and simulation semantics across the standard.

Integration:
- sv-tests is added as a git submodule under `test/sv-tests/`
- CI runs the sv-tests harness against the `deltahdl` binary
- Results are tracked per test to measure standard coverage over time

## 13. Synthesis Engine

### 13.1 Synthesizable Subset

Only a subset of SystemVerilog is synthesizable. The synthesis path accepts:

| Construct | Synthesizable | Maps to |
|-----------|:---:|---------|
| `always_comb` | Yes | Combinational logic |
| `always_ff` | Yes | Flip-flops + next-state logic |
| `always_latch` | Yes | Latches + enable logic |
| `assign` (continuous) | Yes | Combinational logic |
| Module instantiation | Yes | Hierarchical cells |
| Gate primitives | Yes | Logic gates |
| `generate` for/if/case | Yes | Unrolled at elaboration |
| Parameters, localparam | Yes | Constants at elaboration |
| Packed arrays, structs, enums | Yes | Bit vectors |
| `if`/`else`, `case`, `?:` | Yes | Muxes / priority logic |
| Arithmetic operators | Yes | Adders, multipliers, comparators |
| Bitwise/logical operators | Yes | Gate-level logic |
| `initial` blocks | No | Rejected |
| `#delay`, `@(event)` timing | No | Rejected (except `always_ff` edge list) |
| `fork`/`join` | No | Rejected |
| System tasks (`$display`, etc.) | No | Ignored with warning |
| Classes, dynamic arrays, strings | No | Rejected |
| `real`/`shortreal` types | No | Rejected |
| `force`/`release`, `assign`/`deassign` | No | Rejected |

### 13.2 Logic Network Representation

The synthesis IR is an **And-Inverter Graph (AIG)** — a DAG where every node is
either a primary input, a 2-input AND gate, or an inverter (edge attribute):

```cpp
struct AigNode {
    uint32_t id;
    uint32_t fanin0;        // node ID, LSB = complement flag
    uint32_t fanin1;        // node ID, LSB = complement flag
};

struct AigGraph {
    std::vector<AigNode> nodes;
    std::vector<uint32_t> inputs;   // primary input node IDs
    std::vector<uint32_t> outputs;  // primary output literals
    std::vector<uint32_t> latches;  // (current, next, init) triples
};
```

AIG is chosen because:
- Universal (any Boolean function decomposes to AND + NOT)
- Compact representation enabling O(n) graph traversals
- Well-studied optimization algorithms (rewriting, refactoring, balancing)
- Direct interface to ABC and other logic optimization tools

### 13.3 Synthesis Pipeline

```
RTLIR (synthesizable subset)
    │
    ▼
┌───────────────────┐
│ Process Flattening│  always_comb → logic cones, always_ff → FF + next-state
└──────┬────────────┘
       │  register-transfer list + combinational equations
       ▼
┌───────────────────┐
│  AIG Construction │  Boolean equations → And-Inverter Graph
└──────┬────────────┘
       │  raw AIG
       ▼
┌───────────────────┐
│ Logic Optimization│  Rewriting, refactoring, balancing, redundancy removal
└──────┬────────────┘
       │  optimized AIG
       ▼
┌───────────────────┐
│ Technology Mapping│  AIG → cells from target library (LUTs or std cells)
└──────┬────────────┘
       │  mapped netlist
       ▼
┌───────────────────┐
│  Netlist Output   │  Verilog, BLIF, JSON (nextpnr), EDIF
└───────────────────┘
```

### 13.4 Logic Optimization Passes

Applied iteratively until convergence (area or delay target met):

| Pass | Purpose | Complexity |
|------|---------|-----------|
| **AIG rewriting** | Replace small subgraphs with cheaper equivalents using NPN-class lookup | O(n) per sweep |
| **AIG refactoring** | Recompute node functions using larger cuts for better sharing | O(n * k) |
| **AIG balancing** | Restructure tree-like cones to minimize depth | O(n log n) |
| **Redundancy removal** | SAT-based or simulation-based identification of stuck-at faults | O(n * SAT) |
| **Constant propagation** | Eliminate nodes with constant inputs | O(n) |
| **Structural hashing** | Merge duplicate AND nodes | O(n) amortized |

### 13.5 Technology Mapping

Two mapping targets:

**FPGA (LUT-based)**:
- K-LUT mapping using priority-cut enumeration
- Targets configurable LUT size (typically K=4 or K=6)
- Area-oriented: minimize LUT count
- Delay-oriented: minimize critical path depth

**ASIC (standard cell)**:
- Library-based mapping using cell pattern matching on AIG cuts
- Reads Liberty (.lib) timing/area models
- Iterative delay-area tradeoff optimization

### 13.6 Output Formats

| Format | Purpose |
|--------|---------|
| **Verilog netlist** | Gate-level Verilog for simulation or downstream tools |
| **BLIF** | Berkeley Logic Interchange Format (ABC, academic tools) |
| **JSON** | nextpnr interchange format for FPGA place-and-route |
| **EDIF** | Electronic Design Interchange Format (vendor tools) |

### 13.7 Synthesis CLI Options

```
deltahdl --synth [synth-options] <source-files...>

Synth Options:
  --synth                Enable synthesis mode (instead of simulation)
  --target <fpga|asic>   Mapping target (default: fpga)
  --lut-size <K>         LUT input count for FPGA mapping (default: 6)
  --lib <file.lib>       Liberty cell library for ASIC mapping
  --top <module>         Top-level module to synthesize
  --output <file>        Output netlist file
  --format <fmt>         Output format: verilog, blif, json, edif (default: verilog)
  --no-opt               Skip logic optimization passes
  --area                 Optimize for area (default)
  --delay                Optimize for delay
  --dump-aig             Dump AIG before/after optimization (debug)
  --retime               Enable register retiming
```

## 14. Incremental Development Roadmap

### Phase 1: Hello DeltaHDL

Goal: `$display("Hello, DeltaHDL!");` runs from a `.sv` file.

Delivers: preprocessor (basic), lexer, parser (module + initial + $display only),
trivial elaboration, scheduler skeleton (Active region only), coroutine process.

```systemverilog
module hello;
  initial $display("Hello, DeltaHDL!");
endmodule
```

### Phase 2: Combinational Logic

Goal: continuous assignments, wire nets, basic expressions, gate primitives.

Delivers: expression evaluation (all operators from §11), wire resolution,
`assign` statements, `always_comb` with inferred sensitivity, VCD output.

```systemverilog
module mux2(input logic a, b, sel, output logic y);
  assign y = sel ? b : a;
endmodule
```

### Phase 3: Sequential Logic

Goal: flip-flops, clocks, nonblocking assignments, `#delay`, `@(posedge/negedge)`.

Delivers: full scheduler (all 17 regions), NBA scheduling, `always_ff`,
`always_latch`, `initial` with delays, `fork`/`join`.

```systemverilog
module counter #(parameter WIDTH = 8)(input logic clk, rst, output logic [WIDTH-1:0] count);
  always_ff @(posedge clk or posedge rst)
    if (rst) count <= '0;
    else count <= count + 1;
endmodule
```

### Phase 4: Hierarchy and Types

Goal: module instantiation, parameters, generate, packed/unpacked arrays,
structs, enums, interfaces.

Delivers: full elaboration engine, parameterized modules, generate for/if/case,
aggregate data types, interface/modport.

### Phase 5: Combinational Synthesis

Goal: synthesize combinational-only designs to a Verilog gate-level netlist.

Delivers: synthesizability checker, `always_comb`/`assign` flattening, AIG
construction, structural hashing, constant propagation, AIG rewriting,
FPGA LUT mapping, Verilog netlist output.

```systemverilog
module adder(input logic [7:0] a, b, output logic [8:0] sum);
  assign sum = a + b;
endmodule
```

### Phase 6: Sequential Synthesis

Goal: synthesize `always_ff` and `always_latch` designs with register inference.

Delivers: flip-flop/latch inference from `always_ff`/`always_latch`, memory
inference from array patterns, AIG balancing and refactoring passes,
ASIC standard-cell mapping with Liberty (.lib) reader, BLIF/JSON output.

### Phase 7: Advanced Simulation Features

Goal: classes, dynamic arrays, associative arrays, strings, tasks/functions,
clocking blocks, assertions (basic), DPI-C.

### Phase 8: Optimization

Goal: simulation and synthesis performance.

Delivers (simulation): 2-state fast path, event coalescing, compiled-code
simulation for hot processes, multi-threaded partition-based simulation.

Delivers (synthesis): register retiming, redundancy removal, delay-oriented
mapping, iterative area-delay tradeoff.
