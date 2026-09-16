#include "elaborator/elaborator_process_validate.h"

#include <format>
#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

namespace {

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
bool StmtHasForkJoin(const Stmt* stmt) {
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
std::string_view AssignedVariable(const Expr* lhs) {
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
void CollectAssignedVariables(const Stmt* stmt, AssignedNames& out) {
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
void KeepOnlyCommon(AssignedNames& acc, const AssignedNames& other) {
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
void KeepBoth(AssignedNames& acc, const AssignedNames& other) {
  acc.insert(other.begin(), other.end());
}

AssignedNames AssignedOnEveryPath(const Stmt* stmt);

// §9.3.2's Table 9-1 gives the three join keywords their meanings. Under `join`
// "the parent process blocks until all the processes spawned by this fork
// terminate", so control leaves the block only once every arm has run and the
// arms contribute everything each of them contributes. Under `join_any` the
// parent blocks "until any one of the processes spawned by this fork
// terminates" and under `join_none` it "continues to execute concurrently with
// all the processes spawned by the fork", so under either one an arm's
// assignment need not have been made when control passes on, and the fork
// establishes nothing.
AssignedNames AssignedOnEveryForkPath(const Stmt* stmt) {
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
AssignedNames AssignedOnEveryForPath(const Stmt* stmt) {
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
AssignedNames AssignedOnEveryCasePath(const Stmt* stmt) {
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
AssignedNames AssignedOnEveryPath(const Stmt* stmt) {
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
bool InfersLatch(const Stmt* body) {
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
bool StmtBlocks(const Stmt* stmt, bool include_intra_assign = false);

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
bool StmtBlocks(const Stmt* stmt, bool include_intra_assign) {
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

void ValidateCombLatchProcess(ModuleItem* item, const RtlirProcess& proc,
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
void ValidateAlwaysFFProcess(ModuleItem* item, const RtlirProcess& proc,
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
  // §16.14.5: a static concurrent assertion is modelled on an always_ff
  // process for its always semantics, its clocking event any event
  // expression §16.5 allows, so the edge §9.2.2.4 expects of sequential
  // logic is not asked of it.
  bool concurrent = proc.body != nullptr && proc.body->is_concurrent_clocked;
  if (!proc.sensitivity.empty() && !has_edge && !concurrent) {
    diag.Warning(item->loc,
                 "always_ff has no edge-sensitive event; "
                 "may not represent sequential logic",
                 Subclause("9.2.2.4"));
  }
}

void ValidateFinalProcess(ModuleItem* item, const RtlirProcess& proc,
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

}  // namespace

void ValidateProcess(RtlirProcessKind kind, ModuleItem* item,
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

}  // namespace delta
