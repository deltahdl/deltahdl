#include <format>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/global_clock_assertion_event.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "lexer/token.h"
#include "parser/ast.h"

namespace delta {

RtlirNet MakeImplicitPortNet(std::string_view name, uint32_t port_width,
                             bool port_is_signed, NetType default_nettype) {
  RtlirNet net;
  net.name = name;
  // §6.10: an implicit net assumed for a port expression takes the default net
  // type and the vector width of the port expression declaration.
  net.net_type = default_nettype;
  net.width = port_width == 0 ? 1 : port_width;
  // §23.2.2.1: nets connected to ports without an explicit net declaration are
  // unsigned unless the port itself is declared signed.
  net.is_signed = port_is_signed;
  return net;
}

uint32_t LookupLhsWidth(const Expr* lhs, const RtlirModule* mod) {
  if (!lhs || lhs->kind != ExprKind::kIdentifier) return 0;
  for (const auto& v : mod->variables) {
    if (v.name == lhs->text) return v.width;
  }
  for (const auto& n : mod->nets) {
    if (n.name == lhs->text) return n.width;
  }
  for (const auto& p : mod->ports) {
    if (p.name == lhs->text) return p.width;
  }
  return 0;
}

RtlirProcessKind MapAlwaysKind(AlwaysKind ak) {
  switch (ak) {
    case AlwaysKind::kAlways:
      return RtlirProcessKind::kAlways;
    case AlwaysKind::kAlwaysComb:
      return RtlirProcessKind::kAlwaysComb;
    case AlwaysKind::kAlwaysFF:
      return RtlirProcessKind::kAlwaysFF;
    case AlwaysKind::kAlwaysLatch:
      return RtlirProcessKind::kAlwaysLatch;
  }
  return RtlirProcessKind::kAlwaysComb;
}

// §9.2.2.2.2 rules that statements in an always_comb "shall not include ...
// fork-join statements", §9.2.2.3 applies that to always_latch, §9.2.2.4 states
// it of always_ff and §9.2.3 of a final procedure. None of the four names a
// statement the bar is lifted inside, so this descends every link
// ForEachChildStmt in elaborator_validate_internal.h names. It wrote out six of
// the thirteen, so a fork nested in another fork's arm, in a for initialization
// or step, in a randcase item, in either arm of an assertion action block or in
// a randsequence production was never looked at.
//
// ForEachChildStmt gives the visitor no way to stop, so the first fork found is
// kept in `found` and the recursion runs only while `found` is false.
static bool StmtHasForkJoin(const Stmt* stmt) {
  if (!stmt) return false;
  if (stmt->kind == StmtKind::kFork) return true;
  bool found = false;
  ForEachChildStmt(stmt, [&](Stmt* const& sub) {
    if (found) return;
    found = StmtHasForkJoin(sub);
  });
  return found;
}

using AssignedNames = std::unordered_set<std::string_view>;

// The variable a procedural assignment writes, named by the leftmost identifier
// of its target. A select or a member access is read down to that identifier
// rather than kept whole: a path that writes one bit or one field of a variable
// that another path wrote entire has not left the variable unassigned, and
// telling those two targets apart here would report a latch that is not there.
static std::string_view AssignedVariable(const Expr* lhs) {
  const Expr* e = lhs;
  while (e) {
    if (e->kind == ExprKind::kIdentifier) return e->text;
    // A select keeps what it indexes in `base`; a member access keeps the
    // object it selects from in `lhs`, with `rhs` naming the member.
    if (e->kind == ExprKind::kSelect) {
      e = e->base;
      continue;
    }
    if (e->kind == ExprKind::kMemberAccess) {
      e = e->lhs;
      continue;
    }
    break;
  }
  return {};
}

// Every variable the body assigns anywhere, whatever path reaches it.
//
// §9.2.2.2 and §9.2.2.3 ask what values the procedure leaves behind and put no
// condition on which statement an assignment stands in, so this descends every
// link ForEachChildStmt in elaborator_validate_internal.h names. It wrote out
// six of the thirteen, so a variable assigned only in a fork arm, a for
// initialization or step, a randcase item, an assertion action block or a
// randsequence production was invisible to InfersLatch below, and neither the
// always_comb warning nor the always_latch one could reach it.
static void CollectAssignedVariables(const Stmt* stmt, AssignedNames& out) {
  if (!stmt) return;
  if (stmt->kind == StmtKind::kBlockingAssign ||
      stmt->kind == StmtKind::kNonblockingAssign) {
    auto name = AssignedVariable(stmt->lhs);
    if (!name.empty()) out.insert(name);
  }
  ForEachChildStmt(
      stmt, [&](Stmt* const& sub) { CollectAssignedVariables(sub, out); });
}

// Drops from `acc` every name `other` does not also hold, leaving what the two
// branches of a choice agree on.
static void KeepOnlyCommon(AssignedNames& acc, const AssignedNames& other) {
  for (auto it = acc.begin(); it != acc.end();) {
    if (other.find(*it) == other.end()) {
      it = acc.erase(it);
    } else {
      ++it;
    }
  }
}

// Adds to `acc` every name `other` holds, for a statement that runs whenever
// the statement before it ran.
static void KeepBoth(AssignedNames& acc, const AssignedNames& other) {
  acc.insert(other.begin(), other.end());
}

static AssignedNames AssignedOnEveryPath(const Stmt* stmt);

// §9.3.2's Table 9-1 gives the three join keywords their meanings. Under `join`
// "the parent process blocks until all the processes spawned by this fork
// terminate", so control leaves the block only once every arm has run and the
// arms contribute everything each of them contributes. Under `join_any` the
// parent blocks "until any one of the processes spawned by this fork
// terminates" and under `join_none` it "continues to execute concurrently with
// all the processes spawned by the fork", so under either one an arm's
// assignment need not have been made when control passes on, and the fork
// establishes nothing.
static AssignedNames AssignedOnEveryForkPath(const Stmt* stmt) {
  AssignedNames out;
  if (stmt->join_kind != TokenKind::kKwJoin) return out;
  for (const auto* s : stmt->fork_stmts) KeepBoth(out, AssignedOnEveryPath(s));
  return out;
}

// §12.7.1 controls the for-loop "by a three-step process": step a) "executes
// one or more for_initialization assignments", once and under no condition;
// step b) tests the expression and executes the body; step c) "executes one or
// more for_step assignments ... then repeats step b)". So an initialization
// assignment is made on every path through the statement, and a step assignment
// is made once the body has run, which the note below counts as taken.
static AssignedNames AssignedOnEveryForPath(const Stmt* stmt) {
  AssignedNames out;
  for (const auto* s : stmt->for_inits) KeepBoth(out, AssignedOnEveryPath(s));
  KeepBoth(out, AssignedOnEveryPath(stmt->for_body));
  for (const auto* s : stmt->for_steps) KeepBoth(out, AssignedOnEveryPath(s));
  return out;
}

// A case statement covers every path only if it has a default item: without one
// there is a way through the statement that runs no item at all, and that way
// assigns nothing. With one, a variable survives only where every item, the
// default included, assigns it.
static AssignedNames AssignedOnEveryCasePath(const Stmt* stmt) {
  AssignedNames common;
  bool has_default = false;
  for (const auto& ci : stmt->case_items)
    if (ci.is_default) has_default = true;
  if (!has_default) return common;
  bool started = false;
  for (const auto& ci : stmt->case_items) {
    AssignedNames item = AssignedOnEveryPath(ci.body);
    if (started) {
      KeepOnlyCommon(common, item);
      continue;
    }
    common = item;
    started = true;
  }
  return common;
}

// The variables `stmt` assigns on every path through it. Statements in sequence
// contribute everything each of them contributes; a choice contributes only
// what all of its arms agree on, and an arm that is not written at all -- an if
// without an else, a case without a default -- contributes nothing.
//
// A loop body counts as taken. A loop that might run no iterations would make
// every assignment inside it conditional, and this check exists to identify a
// latch, so reading a loop as skipped would report latches that are not there.
//
// This walk does not take its list of children from ForEachChildStmt in
// elaborator_validate_internal.h, and the licence for that is the sentence
// above ForEachChildStmt about saying so in a comment rather than writing a
// shorter list silently. The answer here is a union over some of the thirteen
// statement links and an intersection over others, and a visitor handed a bare
// child cannot tell which link it came from, which is the same reason
// ForEachChildExpr's own comment gives for a walk whose rule turns on the field
// an expression stood in. So the links are written out with the clause that
// decides each, and three of them contribute nothing on purpose:
//
//  - Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. §16.3 has the pass
//    statement "executed if the expression evaluates to true" and the fail
//    statement "executed if the expression evaluates to false", which between
//    them would cover the expression's whole domain, but §20.11 gives
//    $assertcontrol "the capability to enable/disable action block execution of
//    assertions and expect statements". So there is a way through the statement
//    that runs neither arm, exactly as there is through a case with no default.
//  - Stmt::randcase_items. §18.16 rules that "if all randcase_items specify
//    zero weights, then no branch is taken", and the weights "can be arbitrary
//    expressions", read while the design runs.
//  - Stmt::rs_productions. §18.17 rules that production lists separated by a
//    "|" "imply a set of choices, which the generator will make at random", so
//    no code block of a randsequence is reached on every path through it.
static AssignedNames AssignedOnEveryPath(const Stmt* stmt) {
  AssignedNames out;
  if (!stmt) return out;
  switch (stmt->kind) {
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign: {
      auto name = AssignedVariable(stmt->lhs);
      if (!name.empty()) out.insert(name);
      return out;
    }
    case StmtKind::kBlock:
      for (const auto* s : stmt->stmts) KeepBoth(out, AssignedOnEveryPath(s));
      return out;
    case StmtKind::kIf:
      if (!stmt->else_branch) return out;
      out = AssignedOnEveryPath(stmt->then_branch);
      KeepOnlyCommon(out, AssignedOnEveryPath(stmt->else_branch));
      return out;
    case StmtKind::kCase:
      return AssignedOnEveryCasePath(stmt);
    case StmtKind::kFork:
      return AssignedOnEveryForkPath(stmt);
    case StmtKind::kFor:
      return AssignedOnEveryForPath(stmt);
    case StmtKind::kForeach:
    case StmtKind::kWhile:
    case StmtKind::kDoWhile:
    case StmtKind::kForever:
    case StmtKind::kRepeat:
      return AssignedOnEveryPath(stmt->body);
    default:
      return out;
  }
}

// §9.2.2.2 asks a tool to "warn if the behavior within an always_comb procedure
// does not represent combinational logic, such as if latched behavior can be
// inferred", and §9.2.2.3 asks the mirror question of always_latch. Both are
// questions about the behavior, which is to say about the values the procedure
// leaves behind rather than about the shape its control flow happens to take.
//
// A variable the procedure assigns somewhere but not on every path keeps its
// previous value on the paths that skip it, and holding a value across an
// execution is what a latch does. A variable assigned on every path is a
// function of the inputs alone. So a body that opens with an unconditional
// assignment and then narrows it in an incomplete if or case still assigns that
// variable on every path, and describes combinational logic however incomplete
// the choice below is.
//
// Assignments made inside a subroutine the body calls are not followed. Reading
// a variable no path assigns is not a latch either: the answer is drawn from
// the variables the body writes.
static bool InfersLatch(const Stmt* body) {
  AssignedNames assigned;
  CollectAssignedVariables(body, assigned);
  AssignedNames every_path = AssignedOnEveryPath(body);
  for (auto name : assigned)
    if (every_path.find(name) == every_path.end()) return true;
  return false;
}

// Detects a statement that suspends the process executing it, whether through a
// statement-level timing control (delay, cycle delay, event control, wait, wait
// fork) or on its own (wait_order, expect). §9.2.2.2.2 rules that statements in
// an always_comb "shall not include those that block, have blocking timing or
// event controls", so blocking is the property the callers ask about and a
// timing control is one way of having it.
//
// When `include_intra_assign` is set, an assignment carrying an
// intra-assignment timing control (`x = #5 y;`, `x <= @(clk) y;`, `x = ##2 y;`,
// the repeat-event form) also counts — a form legal for some always procedures
// (e.g. a nonblocking delay in always_comb, §9.2.2.2) but not for a final
// procedure, which is limited to the timing-free statements permitted in a
// function.
static bool StmtBlocks(const Stmt* stmt, bool include_intra_assign = false);

// §9.2.2.2.2 states its rule of "statements in an always_comb", §9.2.2.4 of the
// statements of an always_ff and §9.2.3 of those a final procedure holds; none
// of the three names a statement the rule is suspended inside, so this descends
// every link ForEachChildStmt in elaborator_validate_internal.h names. It wrote
// out seven of the thirteen, so a delay, a cycle delay, an event control, a
// wait, a wait_order or an expect written in a for initialization or step, in a
// randcase item, in either arm of an assertion action block or in a
// randsequence production stood in an always_comb, an always_ff and a final
// procedure unreported.
//
// ForEachChildStmt gives the visitor no way to stop, so the first blocking
// statement found is kept in `found` and the recursion runs only while `found`
// is false.
static bool StmtBlocks(const Stmt* stmt, bool include_intra_assign) {
  if (!stmt) return false;
  switch (stmt->kind) {
    // §14.11 makes a cycle delay a procedural timing control that "shall wait
    // for the specified number of clocking block events", §15.5.4 has
    // wait_order "suspend the calling process" until its events trigger, and
    // §16.17 calls expect "a procedural blocking statement".
    //
    // kNbEventTrigger is absent by decision rather than by oversight: §15.5.1
    // rules that with the `->>` operator "the statement executes without
    // blocking", so a nonblocking event trigger does not suspend the process
    // and none of the callers' rules reach it.
    case StmtKind::kTimingControl:
    case StmtKind::kDelay:
    case StmtKind::kCycleDelay:
    case StmtKind::kEventControl:
    case StmtKind::kWait:
    case StmtKind::kWaitOrder:
    case StmtKind::kWaitFork:
    case StmtKind::kExpect:
      return true;
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
      return include_intra_assign &&
             (stmt->delay != nullptr || stmt->cycle_delay != nullptr ||
              !stmt->events.empty());
    default:
      break;
  }
  bool found = false;
  ForEachChildStmt(stmt, [&](Stmt* const& sub) {
    if (found) return;
    found = StmtBlocks(sub, include_intra_assign);
  });
  return found;
}

static void ValidateCombLatchProcess(ModuleItem* item, const RtlirProcess& proc,
                                     RtlirProcessKind kind, DiagEngine& diag) {
  if (kind != RtlirProcessKind::kAlwaysComb &&
      kind != RtlirProcessKind::kAlwaysLatch)
    return;
  const bool kIsComb = kind == RtlirProcessKind::kAlwaysComb;
  const char* kw = kIsComb ? "always_comb" : "always_latch";
  // The keyword a message names and the subclause a report cites are chosen
  // together, from one condition, so a report added here cannot name one
  // construct and send the reader to the other's rules.
  //
  // §9.2.2.2.2 "always_comb compared to always @*" states these three rules --
  // "Statements in an always_comb shall not include those that block, have
  // blocking timing or event controls, or fork-join statements" -- and every
  // sentence in it is about always_comb. It never mentions always_latch. What
  // binds them to always_latch is one sentence in §9.2.2.3 "Latched logic
  // always_latch procedure": "All statements in 9.2.2.2 shall apply to
  // always_latch." So §9.2.2.3 is the subclause a reader of an always_latch
  // report has to open, and §9.2.2.2.2 the one a reader of an always_comb
  // report has to.
  const Subclause kRule =
      kIsComb ? Subclause("9.2.2.2.2") : Subclause("9.2.2.3");
  // An always_comb or always_latch infers its own sensitivity and shall not
  // carry an explicit event control; the parser stores such a control in the
  // block's sensitivity list.
  if (!item->sensitivity.empty() || item->is_star_sensitivity) {
    diag.Error(item->loc,
               std::format("{} shall not have an explicit event control", kw),
               kRule);
  }
  if (StmtBlocks(proc.body)) {
    diag.Error(item->loc,
               std::format("{} shall not contain timing controls", kw), kRule);
  }
  if (StmtHasForkJoin(proc.body)) {
    diag.Error(item->loc,
               std::format("{} shall not contain fork-join statements", kw),
               kRule);
  }
  if (kIsComb && InfersLatch(proc.body)) {
    diag.Warning(item->loc,
                 "always_comb may infer latched behavior; "
                 "ensure all paths assign all outputs",
                 Subclause("9.2.2.2"));
  }
  if (!kIsComb && !InfersLatch(proc.body)) {
    diag.Warning(item->loc,
                 "always_latch does not infer latched behavior; "
                 "ensure incomplete assignments create intended latches",
                 Subclause("9.2.2.3"));
  }
}

// §9.2.2.4's rules are read off proc.sensitivity, not item->sensitivity:
// BuildProcessWithSensitivity substitutes the effective global clocking
// declaration's event expression onto the process's own copy (§14.14). Read off
// item->sensitivity, an `always_ff @($global_clock)` would be judged on the
// argument-less system call the parser left there, which carries no edge.
static void ValidateAlwaysFFProcess(ModuleItem* item, const RtlirProcess& proc,
                                    DiagEngine& diag) {
  if (proc.sensitivity.empty()) {
    diag.Error(item->loc, "always_ff requires an event control",
               Subclause("9.2.2.4"));
  }
  if (StmtBlocks(proc.body)) {
    diag.Error(item->loc,
               "always_ff shall not contain blocking timing controls",
               Subclause("9.2.2.4"));
  }
  if (StmtHasForkJoin(proc.body)) {
    diag.Error(item->loc, "always_ff shall not contain fork-join statements",
               Subclause("9.2.2.4"));
  }
  bool has_edge = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.edge == Edge::kPosedge || ev.edge == Edge::kNegedge) {
      has_edge = true;
      break;
    }
  }
  if (!proc.sensitivity.empty() && !has_edge) {
    diag.Warning(item->loc,
                 "always_ff has no edge-sensitive event; "
                 "may not represent sequential logic",
                 Subclause("9.2.2.4"));
  }
}

static void ValidateFinalProcess(ModuleItem* item, const RtlirProcess& proc,
                                 DiagEngine& diag) {
  if (StmtBlocks(proc.body, /*include_intra_assign=*/true)) {
    diag.Error(item->loc, "final procedure shall not contain timing controls",
               Subclause("9.2.3"));
  }
  if (StmtHasForkJoin(proc.body)) {
    diag.Error(item->loc,
               "final procedure shall not contain fork-join statements",
               Subclause("9.2.3"));
  }
}

// §14.14: an event control naming $global_clock in the procedure body waits on
// the event expression of the global clocking declaration in scope, so it is
// rewritten into that expression here, where the body reaches the process.
//
// The rewrite is made on a copy of the statement rather than in place because
// `item` belongs to the one ModuleDecl the parser built for the module, while
// Elaborator::ElaborateModule runs once per instantiation of it: every
// instance of a module builds its processes from the same Stmt objects, so a
// statement written in place would carry one instance's substitution into
// every other instance. Keep any further per-instance rewrite of a process
// body on a copy for the same reason.
//
// SubstituteGlobalClockEventControls returns `item->body` itself where nothing
// was rewritten, which is every procedure that does not name $global_clock, so
// the copy costs an allocation only where the rewrite is actually made.
static Stmt* BuildProcessBody(const ModuleItem* item,
                              const ProcessBuildEnv& env) {
  if (env.global_clocking_event == nullptr) return item->body;
  return SubstituteGlobalClockEventControls(
      item->body, *env.global_clocking_event, env.arena);
}

static RtlirProcess BuildProcessWithSensitivity(RtlirProcessKind kind,
                                                ModuleItem* item,
                                                const ProcessBuildEnv& env) {
  RtlirProcess proc;
  proc.kind = kind;
  proc.loc = item->loc;
  proc.body = BuildProcessBody(item, env);
  proc.sensitivity = item->sensitivity;
  // §14.14: a procedure whose sensitivity list is the single clocking event
  // $global_clock waits on the effective global clocking declaration's event
  // expression. The substitution is made on the process's own copy because
  // `item` belongs to the one ModuleDecl the parser built for the module while
  // this runs once per instantiation, and rule b) can give two instances
  // different events; writing `item` would give both whichever came first.
  if (env.global_clocking_event != nullptr) {
    SubstituteGlobalClockLeadingEvent(proc.sensitivity,
                                      *env.global_clocking_event);
  }
  proc.is_star_sensitivity = item->is_star_sensitivity;
  bool needs_infer = (kind == RtlirProcessKind::kAlwaysComb ||
                      kind == RtlirProcessKind::kAlwaysLatch);
  if (needs_infer && proc.sensitivity.empty()) {
    proc.sensitivity = InferSensitivity(proc.body, env.arena, env.func_map,
                                        true, env.const_names);
  }
  if (kind == RtlirProcessKind::kAlways && item->is_star_sensitivity &&
      proc.sensitivity.empty()) {
    proc.sensitivity =
        InferSensitivity(proc.body, env.arena, nullptr, false, env.const_names);
  }
  return proc;
}

static void ValidateProcess(RtlirProcessKind kind, ModuleItem* item,
                            const RtlirProcess& proc, DiagEngine& diag) {
  if (kind == RtlirProcessKind::kAlways && item->sensitivity.empty() &&
      !item->is_star_sensitivity && !StmtBlocks(proc.body)) {
    diag.Warning(item->loc,
                 "always block has no timing control; may cause "
                 "a zero-delay loop",
                 Subclause("9.2.2.1"));
  }
  ValidateCombLatchProcess(item, proc, kind, diag);
  if (kind == RtlirProcessKind::kAlwaysFF) {
    ValidateAlwaysFFProcess(item, proc, diag);
  }
  if (kind == RtlirProcessKind::kFinal) {
    ValidateFinalProcess(item, proc, diag);
  }
}

void AddProcess(RtlirProcessKind kind, ModuleItem* item, RtlirModule* mod,
                const ProcessBuildEnv& env) {
  RtlirProcess proc = BuildProcessWithSensitivity(kind, item, env);
  ValidateProcess(kind, item, proc, env.diag);
  proc.attrs = ResolveAttributes(item->attrs, env.diag);
  mod->processes.push_back(proc);
}

// Collects the longest static prefix (§11.5.3) of every assignment target
// written in `stmt` or in any statement nested inside it.
//
// §9.2.2.2 states its rule of "the variables assigned on the left-hand side of
// assignments" and §10.3.2 of "any procedural assignment"; neither puts a
// condition on which statement the assignment stands in, so every position a
// statement holds a statement in is a position this collection reaches.
//
// This is a collector, so a position it does not reach costs a name rather than
// a report. The callers below compare the names gathered here against each
// other and against the continuous-assignment targets, and a name that was
// never gathered overlaps nothing: a variable assigned only in the unreached
// position stays absent from every set, so §9.2.2.2's "shall not be assigned by
// any other process" and §10.3.2's "It shall be an error for a variable driven
// by a continuous assignment or output to have ... any procedural assignment"
// both pass it in silence, however many drivers it has. The unreached position
// is an exemption from the single-driver rule rather than a missing diagnostic.
//
// ForEachChildStmt in elaborator_validate_internal.h states those positions
// once for the whole elaborator, which is why the list is not written out again
// here. The visitor takes `Stmt* const&` because `stmt` is a `const Stmt*`,
// which is how ForEachChildStmt lets a walk that only reads the tree share its
// list with the walks that rewrite it.
static void CollectStmtLhsPrefixes(const Stmt* stmt,
                                   std::unordered_set<std::string>& out,
                                   const ScopeMap& scope) {
  if (!stmt) return;
  if (stmt->kind == StmtKind::kBlockingAssign ||
      stmt->kind == StmtKind::kNonblockingAssign) {
    if (stmt->lhs) {
      // §11.5.3: an indexing select stays inside the longest static prefix only
      // when its index is a constant expression. The module parameter scope is
      // threaded in so that a localparam/parameter index (a constant form of
      // §11.2.1) resolves to a value and keeps the select in the prefix, rather
      // than being mistaken for a run-time index and collapsing the prefix to
      // the base identifier -- which would flag distinct constant-indexed
      // elements as one over-driven target.
      std::string prefix = LongestStaticPrefix(stmt->lhs, scope);
      if (!prefix.empty()) out.insert(std::move(prefix));
    }
  }
  ForEachChildStmt(
      stmt, [&](Stmt* const& sub) { CollectStmtLhsPrefixes(sub, out, scope); });
}

// Collects the name of every subroutine called from `expr` or from any
// expression nested inside it. AnyExprChild in elaborator_validate_internal.h
// states the links an Expr holds, which is why the list is not written out
// again here. This walk named nine of the thirteen, and the four it left out
// are positions a call is written in: `w[3:f()]` puts one in Expr::index_end,
// `q.sum() with (f())` in Expr::with_expr, `{f(){1'b0}}` in Expr::repeat_count,
// and `'{f(): 1}` in Expr::pattern_keys.
static void CollectCallNamesExpr(const Expr* expr,
                                 std::unordered_set<std::string_view>& out) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty())
    out.insert(expr->callee);
  ForEachExprChild(
      expr, [&](const Expr* child) { CollectCallNamesExpr(child, out); });
}

// Collects the name of every subroutine called from `stmt` or from any
// statement nested inside it. §9.2.2.2 says of an always_comb procedure that
// "The variables assigned on the left-hand side of assignments shall not be
// assigned by any other process. This includes variables assigned within
// functions called by the procedure but not those assigned within tasks called
// by the procedure." It states no condition on where in the procedure the call
// is written, so every position a statement holds an expression in is a
// position a call reaches the rule from.
//
// This is a collector, so a position it does not reach costs a name rather than
// a report. CollectFuncLhsPrefixes below takes the names gathered here, and no
// others, as the roots of its search of the function bodies; a function called
// only from an unreached position is therefore never opened, its assignment
// targets never join the procedure's own, and the variables it assigns are
// exempt from that sentence however many other processes assign them. The same
// holds one level down, since the closure re-enters this walk over each
// function body it does open.
//
// ForEachChildExpr states the positions a statement holds an expression in and
// ForEachChildStmt the positions it holds a statement in, both in
// elaborator_validate_internal.h, which is why neither list is written out
// again here. This walk named four of the sixteen expression positions, and the
// twelve it left out are positions a call is written in: `int k = f();` puts
// one in Stmt::var_init, `w[f()] = 1;` under Stmt::lhs, `z <= #(f()) a;` in
// Stmt::delay, `assert (f());` in Stmt::assert_expr, and a case-item pattern
// and a randcase weight each hold one too.
static void CollectCallNamesStmt(const Stmt* stmt,
                                 std::unordered_set<std::string_view>& out) {
  if (!stmt) return;
  ForEachChildExpr(stmt, [&](Expr* const& e) { CollectCallNamesExpr(e, out); });
  ForEachChildStmt(stmt,
                   [&](Stmt* const& sub) { CollectCallNamesStmt(sub, out); });
}

static void CollectFuncLhsPrefixes(const Stmt* body, const FuncMap& funcs,
                                   std::unordered_set<std::string>& out,
                                   const ScopeMap& scope) {
  std::unordered_set<std::string_view> pending;
  CollectCallNamesStmt(body, pending);
  std::unordered_set<std::string_view> visited;
  while (!pending.empty()) {
    std::unordered_set<std::string_view> next;
    for (auto& name : pending) {
      if (visited.count(name)) continue;
      visited.insert(name);
      auto it = funcs.find(name);
      if (it == funcs.end()) continue;
      for (auto* s : it->second->func_body_stmts) {
        CollectStmtLhsPrefixes(s, out, scope);
        CollectCallNamesStmt(s, next);
      }
    }
    pending = std::move(next);
  }
}

static bool PrefixesOverlap(const std::string& a, const std::string& b) {
  if (a == b) return true;
  if (a.size() < b.size())
    return b.compare(0, a.size(), a) == 0 &&
           (b[a.size()] == '.' || b[a.size()] == '[');
  if (b.size() < a.size())
    return a.compare(0, b.size(), b) == 0 &&
           (a[b.size()] == '.' || a[b.size()] == '[');
  return false;
}

struct ProcInfo {
  SourceLoc loc;
  std::unordered_set<std::string> lhs;
  ModuleItemKind kind;
};

// §9.2.2.2/§6.5: the driver targets a module's items contribute, each as a
// longest static prefix (§11.5.3) -- one entry per always_comb/always_latch/
// always_ff process, the targets of every continuous assignment, and the
// targets of every general procedural (always/initial) block.
struct ProcessDriverSets {
  std::vector<ProcInfo>& procs;
  std::unordered_set<std::string>& cont_assign_lhs;
  std::unordered_set<std::string>& general_proc_lhs;
};

static const char* ProcessKindLabel(ModuleItemKind k) {
  switch (k) {
    case ModuleItemKind::kAlwaysFFBlock:
      return "always_ff";
    case ModuleItemKind::kAlwaysLatchBlock:
      return "always_latch";
    default:
      return "always_comb";
  }
}

// §11.5.3: the assignment targets of one always_comb/always_latch/always_ff
// process, as longest static prefixes. A target reached through a function call
// counts as the process's own.
static ProcInfo MakeProcInfo(const ModuleItem* item, const FuncMap* func_map,
                             const ScopeMap& scope) {
  ProcInfo info;
  info.loc = item->loc;
  info.kind = item->kind;
  CollectStmtLhsPrefixes(item->body, info.lhs, scope);
  if (func_map && !func_map->empty())
    CollectFuncLhsPrefixes(item->body, *func_map, info.lhs, scope);
  return info;
}

static void CollectProcessLhsInfo(const ModuleDecl* decl,
                                  const ProcessDriverSets& drivers,
                                  const FuncMap* func_map,
                                  const ScopeMap& scope) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock) {
      drivers.procs.push_back(MakeProcInfo(item, func_map, scope));
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_lhs) {
      std::string prefix = LongestStaticPrefix(item->assign_lhs, scope);
      if (!prefix.empty()) drivers.cont_assign_lhs.insert(std::move(prefix));
    }
    // §9.2.2.2: the variables an always_comb assigns "shall not be assigned by
    // any other process". §9.2 makes the general purpose always procedure, the
    // initial procedure and the final procedure each a process, so all three
    // are gathered here; their assignment targets are kept apart from `procs`
    // so an overlap with an always_comb prefix can be flagged. always_comb,
    // always_latch and always_ff are the ones that go into `procs` instead,
    // because a process is also compared against the other two of its own three
    // kinds rather than only against an always_comb.
    if (item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kFinalBlock) {
      CollectStmtLhsPrefixes(item->body, drivers.general_proc_lhs, scope);
    }
  }
}

static void CheckMultiProcDriver(const std::string& prefix, size_t i,
                                 const std::vector<ProcInfo>& procs,
                                 DiagEngine& diag) {
  for (size_t j = i + 1; j < procs.size(); ++j) {
    for (const auto& other : procs[j].lhs) {
      if (PrefixesOverlap(prefix, other)) {
        diag.Error(procs[j].loc,
                   std::format("variable '{}' driven by multiple "
                               "always_comb/always_latch/always_ff "
                               "processes",
                               prefix),
                   Subclause("9.2.2.2"));
        break;
      }
    }
  }
}

static void CheckContAssignConflict(
    const std::string& var, const ProcInfo& proc,
    const std::unordered_set<std::string>& cont_assign_lhs, DiagEngine& diag) {
  for (const auto& ca : cont_assign_lhs) {
    if (PrefixesOverlap(var, ca)) {
      diag.Error(proc.loc,
                 std::format("variable '{}' driven by {} and "
                             "continuous assignment",
                             var, ProcessKindLabel(proc.kind)),
                 Subclause("10.3.2"));
      break;
    }
  }
}

// §9.2.2.2: report an always_comb LHS that is also assigned by a general
// process (a plain always block or an initial block). §9.2.2.3 states that all
// of §9.2.2.2's rules apply to always_latch, so a latch target sharing a prefix
// with a general procedural driver is flagged the same way. always_ff's
// analogous single-driver rule is left to §9.2.2.4. Element granularity comes
// for free from the longest static prefix (§11.5.3): distinct array elements or
// struct fields do not overlap and so are not reported.
static void CheckGeneralProcOverlap(
    const std::string& var, const ProcInfo& proc,
    const std::unordered_set<std::string>& general_proc_lhs, DiagEngine& diag) {
  for (const auto& other : general_proc_lhs) {
    if (PrefixesOverlap(var, other)) {
      diag.Error(proc.loc,
                 std::format("variable '{}' driven by {} and "
                             "another process",
                             var, ProcessKindLabel(proc.kind)),
                 Subclause("9.2.2.2"));
      return;
    }
  }
}

static void CheckGeneralProcConflict(
    const std::vector<ProcInfo>& procs,
    const std::unordered_set<std::string>& general_proc_lhs, DiagEngine& diag) {
  for (const auto& proc : procs) {
    if (proc.kind != ModuleItemKind::kAlwaysCombBlock &&
        proc.kind != ModuleItemKind::kAlwaysLatchBlock)
      continue;
    for (const auto& var : proc.lhs)
      CheckGeneralProcOverlap(var, proc, general_proc_lhs, diag);
  }
}

static void CheckDriverConflicts(
    const std::vector<ProcInfo>& procs,
    const std::unordered_set<std::string>& cont_assign_lhs,
    const std::unordered_set<std::string>& general_proc_lhs, DiagEngine& diag) {
  for (size_t i = 0; i < procs.size(); ++i) {
    for (const auto& var : procs[i].lhs) {
      CheckContAssignConflict(var, procs[i], cont_assign_lhs, diag);
      CheckMultiProcDriver(var, i, procs, diag);
    }
  }
  CheckGeneralProcConflict(procs, general_proc_lhs, diag);
}

void Elaborator::CheckAlwaysCombMultiDriver(const ModuleDecl* decl,
                                            RtlirModule* mod) {
  std::vector<ProcInfo> procs;
  std::unordered_set<std::string> cont_assign_lhs;
  std::unordered_set<std::string> general_proc_lhs;
  // The module parameter scope lets §11.5.3's longest-static-prefix analysis
  // treat a localparam/parameter index as the constant expression it is.
  ScopeMap scope = mod ? BuildParamScope(mod) : ScopeMap{};
  CollectProcessLhsInfo(decl, {procs, cont_assign_lhs, general_proc_lhs},
                        &func_decls_, scope);
  CheckDriverConflicts(procs, cont_assign_lhs, general_proc_lhs, diag_);
}

// §6.5: the single-driver rule is stated per term of a variable's longest
// static prefix, so distinct elements of an aggregate (a struct member or an
// array/part-select element) are independent driver targets. The name-keyed
// cross-checks (ValidateContAssignIdentLhs / ValidateMixedAssignments) collapse
// every element to the base variable name and so can only police whole-variable
// targets; CheckAlwaysCombMultiDriver covers element granularity but only for
// always_comb/always_latch/always_ff processes. This pass closes the remaining
// gap for a continuous assignment whose target is an aggregate element: it
// flags a second continuous driver, or a general procedural (initial / always)
// driver, whose longest static prefix overlaps. Prefixes that are bare
// identifiers stay with the name-keyed checks, and always_comb/latch/ff
// processes stay with CheckAlwaysCombMultiDriver, so no conflict is reported
// twice.
// §6.5: one continuous-assignment target, as a longest static prefix, with a
// note of whether that prefix reaches into an aggregate (a struct member or an
// array/part-select element) rather than naming a whole variable.
struct ContTarget {
  std::string prefix;
  bool aggregate;
  SourceLoc loc;
};

// Gather the continuous-assignment targets of `decl` and the assignment targets
// of its general procedural blocks. always_comb, always_latch, and always_ff
// are left out: CheckAlwaysCombMultiDriver already covers them at element
// granularity. The initial, always and final procedures §9.2 defines have no
// such second pass, so all three are gathered here.
static void CollectAggregateDriverTargets(
    const ModuleDecl* decl, const ScopeMap& scope,
    std::vector<ContTarget>& conts,
    std::unordered_set<std::string>& proc_prefixes) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign && item->assign_lhs) {
      std::string prefix = LongestStaticPrefix(item->assign_lhs, scope);
      if (prefix.empty()) continue;
      bool aggregate = prefix.find('.') != std::string::npos ||
                       prefix.find('[') != std::string::npos;
      conts.push_back({std::move(prefix), aggregate, item->loc});
    }
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kFinalBlock) {
      CollectStmtLhsPrefixes(item->body, proc_prefixes, scope);
    }
  }
}

// Multiple continuous assignments writing to overlapping element prefixes.
// Whole-identifier vs whole-identifier pairs are already diagnosed by
// ValidateContAssignIdentLhs, so at least one side of a reported pair must be
// an aggregate element.
static void CheckOverlappingContTargets(const std::vector<ContTarget>& conts,
                                        DiagEngine& diag) {
  for (size_t i = 0; i < conts.size(); ++i) {
    for (size_t j = i + 1; j < conts.size(); ++j) {
      if (!conts[i].aggregate && !conts[j].aggregate) continue;
      if (PrefixesOverlap(conts[i].prefix, conts[j].prefix)) {
        diag.Error(conts[j].loc,
                   std::format("multiple continuous assignments drive "
                               "overlapping element '{}'",
                               conts[j].prefix),
                   Subclause("10.3.2"));
      }
    }
  }
}

// A continuous assignment to an aggregate element mixed with a procedural
// driver of an overlapping prefix. The whole-identifier form is handled by
// ValidateMixedAssignments, so only aggregate continuous targets are checked.
static void CheckContProcElementMix(
    const std::vector<ContTarget>& conts,
    const std::unordered_set<std::string>& proc_prefixes, DiagEngine& diag) {
  for (const auto& ct : conts) {
    if (!ct.aggregate) continue;
    for (const auto& pp : proc_prefixes) {
      if (PrefixesOverlap(ct.prefix, pp)) {
        diag.Error(ct.loc,
                   std::format("element '{}' has both a continuous assignment "
                               "and a procedural assignment",
                               ct.prefix),
                   Subclause("10.3.2"));
        break;
      }
    }
  }
}

// §6.5: the single-driver rule is stated per term of a variable's longest
// static prefix, so distinct elements of an aggregate (a struct member or an
// array/part-select element) are independent driver targets. The name-keyed
// cross-checks (ValidateContAssignIdentLhs / ValidateMixedAssignments) collapse
// every element to the base variable name and so can only police whole-variable
// targets; CheckAlwaysCombMultiDriver covers element granularity but only for
// always_comb/always_latch/always_ff processes. This pass closes the remaining
// gap for a continuous assignment whose target is an aggregate element: it
// flags a second continuous driver, or a general procedural (initial / always)
// driver, whose longest static prefix overlaps. Prefixes that are bare
// identifiers stay with the name-keyed checks, and always_comb/latch/ff
// processes stay with CheckAlwaysCombMultiDriver, so no conflict is reported
// twice.
void Elaborator::CheckAggregateElementDrivers(const ModuleDecl* decl,
                                              RtlirModule* mod) {
  ScopeMap scope = mod ? BuildParamScope(mod) : ScopeMap{};
  std::vector<ContTarget> conts;
  std::unordered_set<std::string> proc_prefixes;
  CollectAggregateDriverTargets(decl, scope, conts, proc_prefixes);
  CheckOverlappingContTargets(conts, diag_);
  CheckContProcElementMix(conts, proc_prefixes, diag_);
}

}  // namespace delta
