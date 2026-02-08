# DeltaHDL Engine Tasks

## 1. Common Infrastructure

- [x] Arena allocator (bump-pointer, per-phase bulk deallocation)
- [x] 4-value logic types (`Logic4Word`, `Logic4Vec`, dual-rail aval/bval)
- [x] 2-state logic types (`Logic2Vec`)
- [x] Logic operations (AND, OR, XOR, NOT on 4-value vectors)
- [x] `SimTime` with comparison operators
- [x] 17-region `Region` enum (Preponed through Postponed)
- [x] `NetType` enum (wire, wand, wor, tri, tri0, tri1, supply0, supply1, uwire)
- [x] `StrengthVal` struct (strength0/strength1 bit-fields)
- [x] `SourceLoc` and `SourceRange` for diagnostics
- [x] `SourceManager` (multi-file storage, line lookup, location formatting)
- [x] `DiagEngine` (error/warning collection, severity levels, source snippets)
- [ ] Event pool (pre-allocated events recycled after execution)
- [ ] Driver update pool (temporary driver value storage)

## 2. Preprocessor

- [x] `define`, `undef`, `undefineall`
- [x] `include` with recursion depth checking and `-I` path search
- [x] `ifdef`, `ifndef`, `else`, `endif` with conditional stack
- [x] `timescale` (consumed, not yet applied)
- [x] `resetall`
- [x] `MacroTable` (hash-based define/undefine/lookup)
- [ ] `elsif`
- [ ] Function-like macro expansion (parameter substitution)
- [ ] `default_nettype`
- [ ] `celldefine`, `endcelldefine`
- [ ] `unconnected_drive`, `nounconnected_drive`
- [ ] `pragma`
- [ ] `line` (source location override)
- [ ] `__FILE__`, `__LINE__` predefined macros
- [ ] `begin_keywords`, `end_keywords`
- [ ] Apply `timescale` to simulation time precision

## 3. Lexer

- [x] Full token scanning (200+ `TokenKind` values)
- [x] 120 keywords in static hash map
- [x] Simple and escaped identifiers
- [x] Integer literals (decimal, hex, octal, binary, sized/unsized)
- [x] String literals with escape sequences
- [x] System identifiers (`$display`, `$finish`, etc.)
- [x] All single/multi-character operators (60+)
- [x] Line and block comments
- [x] Line/column tracking per token
- [ ] Real literals (fixed-point and exponential)
- [ ] Time literals (`100ns`, `1.5ps`)
- [ ] Remaining ~140 keywords from Annex B

## 4. Parser

- [x] AST node definitions (expressions, statements, declarations, processes)
- [x] Pratt expression parser with IEEE §11 precedence table
- [x] Module declaration parsing (`module`...`endmodule`)
- [x] Port list parsing (direction, type, name)
- [x] `initial` block parsing
- [x] `always`, `always_comb`, `always_ff`, `always_latch` block parsing
- [x] Continuous assignment (`assign`) parsing
- [x] `if`/`else` statement parsing
- [x] Variable and net declarations
- [ ] `case`, `casex`, `casez` statement parsing
- [ ] `for`, `while`, `forever`, `repeat`, `do`...`while` loop parsing
- [ ] `begin`...`end` block parsing with optional labels
- [ ] `fork`...`join`/`join_any`/`join_none` parsing
- [ ] Nonblocking assignment (`<=`) parsing
- [ ] `#delay` and `@(event)` timing control parsing
- [ ] `wait` statement parsing
- [ ] Bit-select and part-select expressions (`a[7:0]`, `a[i+:4]`)
- [ ] Concatenation (`{a, b}`) and replication (`{N{a}}`) expressions
- [ ] System task/function call parsing (`$display(...)`)
- [ ] `function` and `task` declarations
- [ ] Parameter and `localparam` declarations
- [ ] `generate` for/if/case blocks
- [ ] Module instantiation with port connections
- [ ] `interface`, `modport` declarations
- [ ] `package`, `import` declarations
- [ ] `class` declarations
- [ ] `typedef`, `enum`, `struct`, `union` type declarations
- [ ] `program` block parsing
- [ ] Gate primitive instantiation
- [ ] `disable` statement

## 5. Elaboration

- [x] Top-level module resolution by name
- [x] `elaborate()` entry point producing `RtlirDesign`
- [x] `RtlirModule`, `RtlirPort`, `RtlirNet`, `RtlirVariable` node definitions
- [x] `RtlirProcess`, `RtlirContAssign` node definitions
- [x] `type_eval` (bit-width computation, 4-state vs 2-state classification)
- [x] `const_eval` (constant +, -, *, /, %, unary -, +, ~, !)
- [ ] `elaborate_ports()` (create `RtlirPort` from AST port declarations)
- [ ] `elaborate_items()` (create RTLIR nodes from AST module items)
- [ ] Net and variable creation from declarations
- [ ] Continuous assignment elaboration
- [ ] Process elaboration (initial, always, always_comb, always_ff, always_latch)
- [ ] Recursive module instantiation (hierarchy expansion)
- [ ] Parameter override resolution (`#(...)` and `defparam`)
- [ ] `generate for`/`if`/`case` expansion at elaboration time
- [ ] Port binding (implicit continuous assignments, bidirectional connections)
- [ ] Typedef resolution
- [ ] Packed dimension evaluation
- [ ] Sensitivity list inference for `always_comb`/`always_latch` (§9.2.2)
- [ ] Constant expression evaluation for bitwise ops, ternary, shifts
- [ ] Width inference and implicit type promotion

## 6. Simulation Lowering

- [ ] Create `Process` coroutine from each `initial` block
- [ ] Create `Process` coroutine from each `always`/`always_comb`/`always_ff`/`always_latch` block
- [ ] Wrap `always` blocks in implicit infinite loop
- [ ] Create `ContAssignProcess` from each continuous assignment
- [ ] Create `Net` objects with driver lists and resolution functions
- [ ] Create `Variable` objects with storage
- [ ] Build sensitivity map (signal -> list of sensitive processes)
- [ ] Schedule time-zero initialization events into Active region
- [ ] Auto-trigger `always_comb`/`always_latch` at time zero (§9.2)
- [ ] Connect lowered design to scheduler event calendar

## 7. Simulation Execution

- [x] 17-region stratified event scheduler per IEEE §4.5
- [x] `execute_time_slot()` with active/reactive set iteration
- [x] Time-slotted event calendar (`std::map<SimTime, TimeSlot>`)
- [x] Event callbacks via `std::function<void()>`
- [x] C++23 coroutine process model (`SimCoroutine`, `promise_type`)
- [x] `Process` struct (kind, coroutine handle, home region, sensitivity)
- [x] Net resolution: wire/tri, wand/triand, wor/trior
- [x] Variable storage with force/release support
- [ ] `co_await delay(N)` (schedule wakeup at T+N, suspend)
- [ ] `co_await edge(signal, posedge/negedge)` (sensitivity list, suspend)
- [ ] `co_await wait(expr)` (conditional suspend, re-evaluate on wake)
- [ ] `co_await event_trigger(ev)` (named event wait)
- [ ] Blocking assignment execution (inline in Active region)
- [ ] Nonblocking assignment scheduling (RHS in Active, LHS update in NBA)
- [ ] `#0` delay (suspend to Inactive, resume in next Active iteration)
- [ ] `fork`/`join`/`join_any`/`join_none` (child coroutine spawning)
- [ ] Expression evaluation engine (all §11 operators on `Logic4Vec`)
- [ ] Net resolution: tri0, tri1, supply0, supply1, trireg, uwire
- [ ] Strength resolution (§28.12, multi-driver strength comparison)
- [ ] User-defined nettype resolution functions (§6.6.7)
- [ ] `$finish` triggers `final` block execution

## 8. System Tasks

- [x] `$display` (print with newline, format strings: `%d`, `%h`, `%b`, `%s`, `%t`)
- [x] `$write` (print without newline)
- [x] `$finish` (end simulation)
- [x] `$stop` (pause simulation)
- [ ] `$strobe` (print in Postponed region)
- [ ] `$monitor` (print on change in Postponed region)
- [ ] `$time` (return current simulation time)
- [ ] `$realtime` (return current time as real)
- [ ] `$random`, `$urandom`, `$urandom_range`
- [ ] `$readmemh`, `$readmemb` (load memory from file)
- [ ] `$fatal`, `$error`, `$warning`, `$info` (severity tasks)
- [ ] `$dumpfile` (set VCD output file)
- [ ] `$dumpvars` (enable VCD dumping)
- [ ] `$dumpoff`, `$dumpon`, `$dumpall`

## 9. VCD Waveform Output

- [x] VCD file header (`$date`, `$version`, `$timescale`, `$enddefinitions`)
- [x] Signal registration with scope/name/width
- [x] Scope hierarchy writing
- [ ] Value change emission (scalar and vector format)
- [ ] Timestamp writing
- [ ] `$dumpvars` integration with simulation loop

## 10. Synthesis Lowering

- [x] `SynthLower` class structure
- [x] Iterator over continuous assignments and `always_comb` processes
- [ ] Synthesizability checker (reject delays, `initial`, system tasks, classes)
- [ ] `lower_cont_assign()` (expression to AIG translation)
- [ ] `lower_always_comb()` (process flattening to combinational logic cones)
- [ ] `always_ff` lowering (flip-flop + next-state logic extraction)
- [ ] `always_latch` lowering (latch + enable logic extraction)
- [ ] Multi-bit assignment expansion
- [ ] Port I/O mapping to AIG primary inputs/outputs
- [ ] Memory inference (RAM/ROM patterns from array assignments)

## 11. AIG

- [x] `AigNode` and `AigGraph` data structures
- [x] Structural hashing for duplicate node elimination
- [x] `add_and()` with algebraic simplifications
- [x] `add_input()`, `add_not()`, `add_or()`, `add_xor()`, `add_mux()`
- [x] Output and latch registration
- [ ] Constant propagation pass
- [ ] AIG rewriting (4-input cut enumeration, NPN-class lookup, subgraph replacement)
- [ ] AIG refactoring (large cut extraction, BDD decomposition, subgraph replacement)
- [ ] AIG balancing (reverse topological traversal, tree cone collection, balanced reconstruction)
- [ ] Redundancy removal (SAT-based or simulation-based stuck-at fault identification)

## 12. Technology Mapping

- [ ] K-LUT mapping (priority-cut enumeration, configurable LUT size)
- [ ] LUT area-oriented optimization (minimize LUT count)
- [ ] LUT delay-oriented optimization (minimize critical path depth)
- [ ] Liberty (.lib) file parser (tokenizer, cell/pin/timing model extraction)
- [ ] Standard-cell mapping (cell pattern matching on AIG cuts)
- [ ] Delay-area tradeoff optimization

## 13. Netlist Output

- [ ] Verilog netlist writer (gate-level)
- [ ] BLIF writer (Berkeley Logic Interchange Format)
- [ ] JSON writer (nextpnr interchange format)
- [ ] EDIF writer (Electronic Design Interchange Format)

## 14. CLI

- [x] Source file arguments
- [x] `--top <module>`, `--vcd <file>`, `-o <output>`
- [x] `--max-time`, `--seed`, `--synth`, `--lint-only`
- [x] `+define+<name>=<val>`, `+incdir+<path>`
- [x] `-Wall`, `-Werror`, `--version`, `--help`
- [x] Pipeline orchestration (preprocess, parse, elaborate, simulate)
- [ ] `--timescale <t/p>` (override default timescale)
- [ ] `--fst <file>` (FST waveform output via libfst)
- [ ] `-f <file>` (read options from file)
- [ ] `-v <file>`, `-y <dir>` (Verilog library file/directory)
- [ ] `--dump-ast`, `--dump-ir` (debug output)
- [ ] `--synth` mode wired to synthesis pipeline
- [ ] `--target`, `--lut-size`, `--lib`, `--format`, `--no-opt`, `--area`, `--delay`, `--dump-aig`, `--retime`

## 15. Conformance Testing

- [ ] Add CHIPS Alliance sv-tests as git submodule under `test/sv-tests/`
- [ ] CI job to run sv-tests harness against `deltahdl` binary
- [ ] Per-test result tracking

## 16. VPI

- [ ] VPI interface (IEEE 1800-2023 §36-39)

## 17. Advanced Simulation

- [ ] Classes, dynamic arrays, associative arrays, strings
- [ ] `task` and `function` execution
- [ ] Clocking blocks
- [ ] Basic concurrent assertions
- [ ] DPI-C foreign function interface
- [ ] 2-state fast path (skip `bval` for known-2-state designs)
- [ ] Event coalescing
- [ ] Compiled-code simulation for hot processes
- [ ] Multi-threaded partition-based simulation

## 18. Advanced Synthesis

- [ ] Register retiming
- [ ] Delay-oriented mapping
- [ ] Iterative area-delay tradeoff optimization
