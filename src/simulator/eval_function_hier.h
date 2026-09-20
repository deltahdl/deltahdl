#pragma once

// §13.3 with §23.6: a subroutine enabled by hierarchical name into another
// module instance, `u1.tk(3)` with `sub u1();`, runs in that instance. §13.3.2
// keeps the static storage of a static task in one instance apart from the
// same task's in another, so the body's static frame, the bare names it reads
// and §21.2.1.5's %m all resolve in the instance the declaration belongs to,
// not in the instance that wrote the enable; and a task may suspend on a
// timing control while it runs there (§13.3), so the instance is carried by
// the enabling process rather than by the context every process shares.

#include <string>
#include <string_view>

namespace delta {

class Arena;
class SimContext;
struct Expr;
struct GenBlockSubroutineScope;
struct ModuleItem;
struct Variable;

// The declaration a call names and the instance its body runs in.
// `inst_prefix` ends in a `.` and is empty for the top of the design, as
// Process::inst_prefix is; it is the calling instance's for a bare name.
// `gen_block` is the generate block instance's scope for a subroutine one
// declares, reached by the instance's hierarchical name, `blk[1].triple`
// (§27.4 with §23.6), and null for every other target, a bare call from
// inside the block among them, which runs where the caller stands.
struct SubroutineTarget {
  ModuleItem* func = nullptr;
  std::string inst_prefix;
  const GenBlockSubroutineScope* gen_block = nullptr;
};

// The module subroutine `call` names: a bare identifier or a call with a
// bare callee, one through the package scope resolution operator (§26.3), or
// a call whose callee is a dotted path of identifiers, `u1.tk` or `x.u1.tk`,
// resolved relative to the calling instance ahead of the top of the design
// (§23.6 lets the first node be the top of the hierarchy the path is used
// from), or headed by a top-level module's name, `m.t1` from the parallel
// top n (§23.6's complete path), a name in the path followed by an instance
// select, `blk[1].triple` into a loop generate block's instance or `u[2].tk`
// into an instance array's (§23.6). `func` is null where no registered
// declaration answers.
SubroutineTarget FindSubroutineTarget(const Expr* call, SimContext& ctx,
                                      Arena& arena);

// Puts the running process in the instance `target` names, and in the
// generate block instance where the target has one, keeping what it stood
// in, and LeaveCalleeInstance puts that back. Every enter is matched by one
// leave, in reverse, so the two nest with the calls. Neither does anything
// while no process runs, which is where a declaration initializer is
// evaluated and where a unit test sets a call up by hand.
void EnterCalleeInstance(SimContext& ctx, const SubroutineTarget& target);
void LeaveCalleeInstance(SimContext& ctx);

// §27.4: declares the implicit localparam of each loop generate block the
// target's block instance is in as a local of the innermost scope, the
// subroutine's own frame, at the value the loop index had for the instance,
// so the body reads `g` as the block's own processes do; nothing for a
// target of no generate block. Called after the frame is pushed.
void BindGenBlockConsts(const SubroutineTarget& target, SimContext& ctx,
                        Arena& arena);

// The instance the running process stood in before the innermost
// EnterCalleeInstance, and the instance an evaluation stands in where none is
// in force: the one a call's actuals are read in (§13.5) and its output
// arguments written back to (§13.5.2), with the process itself standing in
// the callee's for the static frame key (§13.3.2).
std::string CallerInstancePrefix(SimContext& ctx);

// The three steps of a call that stand in one instance while the process
// stands in the other, each scoped over a step that never suspends: the
// actuals bound (§13.5) and the output arguments written back (§13.5.2) in
// the caller's instance, and a function's body run in the callee's (§13.4).
void BindActualsInCaller(const ModuleItem* func, const Expr* expr,
                         SimContext& ctx, Arena& arena);
void WritebackInCaller(const ModuleItem* func, const Expr* expr,
                       SimContext& ctx, Arena& arena);
void ExecFunctionBodyInCallee(const ModuleItem* func,
                              std::string_view inst_prefix, Variable* ret_var,
                              SimContext& ctx, Arena& arena);

}  // namespace delta
