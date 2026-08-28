// The rules that decide what a hierarchical name may reach, split out of
// elaborator_validate_operations_streaming.cpp, which is named for the Clause
// 11 operators and the §6.24.3 casting rules it holds and had grown a second
// half about something else. §23.6 defines the hierarchical name, and every
// rule below reads one: §23.6 bars a hierarchical reference into a checker,
// §17.7.1 bars a free checker variable from a continuous or blocking
// assignment and any checker variable from an assignment in an initial
// procedure, §24.3 bars a reference to a program signal from outside the
// program, §13.3.1 and §13.4.2 bar a reference to an item of an automatic task
// or function, and §24.5 bars a call to a program subroutine from within a
// design module.

#include <format>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

static std::string_view HierRefLeftmost(const Expr* e) {
  if (e->kind == ExprKind::kIdentifier) return e->text;
  if (e->kind == ExprKind::kMemberAccess && e->lhs)
    return HierRefLeftmost(e->lhs);
  return {};
}

static bool ExprRefersToChecker(
    const Expr* e, const std::unordered_set<std::string_view>& checker_names) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) {
    auto leftmost = HierRefLeftmost(e);
    if (!leftmost.empty() && checker_names.count(leftmost)) return true;
  }
  if (ExprRefersToChecker(e->lhs, checker_names)) return true;
  if (ExprRefersToChecker(e->rhs, checker_names)) return true;
  if (ExprRefersToChecker(e->base, checker_names)) return true;
  for (auto* elem : e->elements) {
    if (ExprRefersToChecker(elem, checker_names)) return true;
  }
  return false;
}

static void WalkStmtsForCheckerRef(
    const Stmt* s, const std::unordered_set<std::string_view>& checker_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->lhs && ExprRefersToChecker(s->lhs, checker_names))
    diag.Error(s->range.start,
               "hierarchical reference into a checker is not permitted",
               Subclause("23.6"));
  if (s->rhs && ExprRefersToChecker(s->rhs, checker_names))
    diag.Error(s->range.start,
               "hierarchical reference into a checker is not permitted",
               Subclause("23.6"));
  // §23.6 ends "Hierarchical references into checkers (see Clause 17) shall
  // not be permitted" and puts no condition on where the reference is written,
  // so every position a statement holds a statement in is one this report
  // reaches. ForEachChildStmt in elaborator_validate_internal.h states those
  // positions once for the whole elaborator, which is why the list is not
  // written out again here. The visitor takes `Stmt* const&` because `s` is a
  // `const Stmt*`.
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForCheckerRef(sub, checker_names, diag);
  });
}

void Elaborator::ValidateHierRefIntoChecker(const ModuleDecl* decl) {
  if (checker_inst_names_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      if (ExprRefersToChecker(item->assign_lhs, checker_inst_names_))
        diag_.Error(item->loc,
                    "hierarchical reference into a checker is not permitted",
                    Subclause("23.6"));
      if (ExprRefersToChecker(item->assign_rhs, checker_inst_names_))
        diag_.Error(item->loc,
                    "hierarchical reference into a checker is not permitted",
                    Subclause("23.6"));
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body)
      WalkStmtsForCheckerRef(item->body, checker_inst_names_, diag_);
  }
}

// §17.7.1: flags any blocking procedural assignment whose target is one of the
// checker's free variables. A free variable may only be updated by a
// nonblocking assignment (from an always_ff procedure), so a blocking
// assignment to it — in any procedure — is illegal.
//
// §17.5 decides which statement positions hold such an assignment in
// conforming source, listing what a checker always procedure may contain:
// blocking and nonblocking assignments, selection statements, loop statements,
// timing event control, subroutine calls, immediate, deferred and concurrent
// assertions, and let declarations. A loop statement is on that list and
// A.6.8's `for_initialization ::= list_of_variable_assignments` puts an
// assignment in a for-loop header; an immediate assertion is on it too, and
// A.6.10's `simple_immediate_assert_statement ::= assert ( expression )
// action_block` with §16.3's `action_block ::= statement_or_null |
// [ statement ] else statement_or_null` puts one in either arm. A randcase
// (§18.16) and a randsequence (A.6.12) are on neither list, so no conforming
// checker always procedure holds one and no test covers the assignment
// §17.7.1 forbids in a randcase item or in a randsequence code block. The walk
// descends them anyway: what a checker procedure may hold is §17.5's rule to
// report, not a reason to keep a shorter list here.
static void WalkStmtsForFreeBlockingAssign(
    const Stmt* s, const std::unordered_set<std::string_view>& free_vars,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign && s->lhs) {
    auto target = HierRefLeftmost(s->lhs);
    if (!target.empty() && free_vars.count(target))
      diag.Error(
          s->range.start,
          std::format("a blocking assignment cannot target free checker "
                      "variable '{}'; a free variable is updated only by "
                      "a nonblocking assignment",
                      target),
          Subclause("17.7.1"));
  }
  // ForEachChildStmt in elaborator_validate_internal.h states Stmt's child
  // statement links once for the whole elaborator, which is why the list is not
  // written out again here.
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForFreeBlockingAssign(sub, free_vars, diag);
  });
}

// §17.7.1: continuous assignments and blocking procedural assignments to a free
// checker variable are illegal; a free variable is left to the nonblocking form
// only. Collects the free (rand) checker variables declared in the checker body
// and rejects any continuous assign or blocking procedural assign that targets
// one. Runs only on checker declarations.
// §17.7.1: a free checker variable is updated only by a nonblocking
// assignment, so a continuous assignment may not target one.
static void CheckContAssignNotFreeVariable(
    const ModuleItem* item,
    const std::unordered_set<std::string_view>& free_vars, DiagEngine& diag) {
  auto target = HierRefLeftmost(item->assign_lhs);
  if (target.empty() || free_vars.count(target) == 0) return;
  diag.Error(item->loc,
             std::format("a continuous assignment cannot target free checker "
                         "variable '{}'; a free variable is updated only by a "
                         "nonblocking assignment",
                         target),
             Subclause("17.7.1"));
}

void Elaborator::ValidateFreeCheckerVariableAssignments(
    const ModuleDecl* decl) {
  if (decl->decl_kind != ModuleDeclKind::kChecker) return;
  std::unordered_set<std::string_view> free_vars;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->is_rand &&
        !item->name.empty())
      free_vars.insert(item->name);
  }
  if (free_vars.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign)
      CheckContAssignNotFreeVariable(item, free_vars, diag_);
    if (IsProceduralItemKind(item->kind) && item->body)
      WalkStmtsForFreeBlockingAssign(item->body, free_vars, diag_);
  }
}

// §17.7.1: flags a blocking or nonblocking assignment inside an initial
// procedure whose target names one of the checker's variables. A checker
// variable may only be initialized in its declaration, never assigned from an
// initial procedure. Variables declared locally inside the initial block are
// not checker variables and so are not in `checker_vars`.
//
// §17.5 decides which statement positions hold an assignment in conforming
// source: "An initial procedure in a checker body may contain let
// declarations, immediate, deferred, and concurrent assertions, and a
// procedural timing control statement using an event control only." A.6.10's
// `simple_immediate_assert_statement ::= assert ( expression ) action_block`
// and §16.3's `action_block ::= statement_or_null | [ statement ] else
// statement_or_null` put an assignment in either arm of an assertion on that
// list. A randcase (§18.16) and a randsequence (A.6.12) are on neither list,
// so no conforming checker initial procedure holds one and no test covers
// either position. The walk descends them anyway: what a checker initial
// procedure may hold is §17.5's rule to report, not a reason to keep a
// shorter list here.
static void WalkStmtsForCheckerVarAssignInInitial(
    const Stmt* s, const std::unordered_set<std::string_view>& checker_vars,
    DiagEngine& diag) {
  if (!s) return;
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs) {
    auto target = HierRefLeftmost(s->lhs);
    if (!target.empty() && checker_vars.count(target))
      diag.Error(s->range.start,
                 std::format("checker variable '{}' cannot be assigned in an "
                             "initial procedure; initialize it in its "
                             "declaration instead",
                             target),
                 Subclause("17.7.1"));
  }
  // ForEachChildStmt in elaborator_validate_internal.h states Stmt's child
  // statement links once for the whole elaborator, which is why the list is not
  // written out again here.
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForCheckerVarAssignInInitial(sub, checker_vars, diag);
  });
}

// §17.7.1: a checker variable may not be assigned in an initial procedure (it
// may only be initialized in its declaration). Collects the variables declared
// in the checker body and rejects any assignment to one of them from an initial
// procedure. Runs only on checker declarations.
void Elaborator::ValidateCheckerVariableInitialAssignment(
    const ModuleDecl* decl) {
  if (decl->decl_kind != ModuleDeclKind::kChecker) return;
  std::unordered_set<std::string_view> checker_vars;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && !item->name.empty())
      checker_vars.insert(item->name);
  }
  if (checker_vars.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock && item->body)
      WalkStmtsForCheckerVarAssignInInitial(item->body, checker_vars, diag_);
  }
}

static bool ExprRefersToProgram(
    const Expr* e, const std::unordered_set<std::string_view>& program_names) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) {
    auto leftmost = HierRefLeftmost(e);
    if (!leftmost.empty() && program_names.count(leftmost)) return true;
  }
  if (ExprRefersToProgram(e->lhs, program_names)) return true;
  if (ExprRefersToProgram(e->rhs, program_names)) return true;
  if (ExprRefersToProgram(e->base, program_names)) return true;
  for (auto* elem : e->elements) {
    if (ExprRefersToProgram(elem, program_names)) return true;
  }
  return false;
}

static void WalkStmtsForProgramRef(
    const Stmt* s, const std::unordered_set<std::string_view>& program_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->lhs && ExprRefersToProgram(s->lhs, program_names))
    diag.Error(s->range.start,
               "hierarchical reference to program signal from outside the "
               "program is not permitted",
               Subclause("24.3"));
  if (s->rhs && ExprRefersToProgram(s->rhs, program_names))
    diag.Error(s->range.start,
               "hierarchical reference to program signal from outside the "
               "program is not permitted",
               Subclause("24.3"));
  // §24.3 says "References to program signals from outside any program block
  // shall be an error" with no condition on where the reference is written, so
  // every position a statement holds a statement in is one this report reaches.
  // ForEachChildStmt in elaborator_validate_internal.h states those positions
  // once for the whole elaborator.
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForProgramRef(sub, program_names, diag);
  });
}

void Elaborator::ValidateHierRefIntoProgram(const ModuleDecl* decl) {
  if (program_inst_names_.empty()) return;
  if (decl->decl_kind == ModuleDeclKind::kProgram) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      if (ExprRefersToProgram(item->assign_lhs, program_inst_names_))
        diag_.Error(item->loc,
                    "hierarchical reference to program signal from outside "
                    "the program is not permitted",
                    Subclause("24.3"));
      if (ExprRefersToProgram(item->assign_rhs, program_inst_names_))
        diag_.Error(item->loc,
                    "hierarchical reference to program signal from outside "
                    "the program is not permitted",
                    Subclause("24.3"));
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body)
      WalkStmtsForProgramRef(item->body, program_inst_names_, diag_);
  }
}

void Elaborator::ValidateAnonymousProgramHierRefs() {
  std::unordered_set<std::string_view> program_names;
  for (const auto* p : unit_->programs) {
    if (!p->name.empty()) program_names.insert(p->name);
  }
  if (program_names.empty()) return;
  for (const auto* item : unit_->cu_items) {
    if (!item->from_anonymous_program) continue;
    if (item->body) WalkStmtsForProgramRef(item->body, program_names, diag_);
    // §24.3: a hierarchical reference to a program from an anonymous program is
    // illegal wherever it appears, including inside a task or function the
    // anonymous program declares (whose body is in func_body_stmts, not body).
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      for (const auto* s : item->func_body_stmts)
        WalkStmtsForProgramRef(s, program_names, diag_);
    }
  }
}

static void CollectHierPathComponents(const Expr* e,
                                      std::vector<std::string_view>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kIdentifier) {
    out.push_back(e->text);
    return;
  }
  if (e->kind == ExprKind::kMemberAccess) {
    CollectHierPathComponents(e->lhs, out);
    CollectHierPathComponents(e->rhs, out);
  }
}

static bool ExprRefersToAutomatic(
    const Expr* e, const std::unordered_set<std::string_view>& auto_names) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) {
    std::vector<std::string_view> components;
    CollectHierPathComponents(e, components);
    for (size_t i = 0; i + 1 < components.size(); ++i) {
      if (auto_names.count(components[i])) return true;
    }
  }
  if (ExprRefersToAutomatic(e->lhs, auto_names)) return true;
  if (ExprRefersToAutomatic(e->rhs, auto_names)) return true;
  if (ExprRefersToAutomatic(e->base, auto_names)) return true;
  for (auto* elem : e->elements) {
    if (ExprRefersToAutomatic(elem, auto_names)) return true;
  }
  return false;
}

// §13.3.1 states the rule for a task and §13.4.2 states it for a function, in
// the same words each time: the items of an automatic subroutine are allocated
// per call and cannot be accessed by hierarchical references. The two are one
// walk over two sets of names, so each set travels with the report its kind of
// subroutine gets.
struct AutoSubroutineRule {
  const std::unordered_set<std::string_view>& names;
  std::string_view message;
  Subclause subclause;
};

// The names of `decl`'s automatic tasks, or of its automatic functions,
// selected by `kind`. Lifetimes have already been defaulted from the enclosing
// declaration (§6.21) by the time this runs, so `is_automatic` is final here.
static std::unordered_set<std::string_view> AutoSubroutineNames(
    const ModuleDecl* decl, ModuleItemKind kind) {
  std::unordered_set<std::string_view> names;
  for (const auto* item : decl->items) {
    if (item->kind == kind && item->is_automatic) names.insert(item->name);
  }
  return names;
}

static void WalkStmtsForAutoRef(const Stmt* s, const AutoSubroutineRule& rule,
                                DiagEngine& diag) {
  if (!s) return;
  if (s->lhs && ExprRefersToAutomatic(s->lhs, rule.names))
    diag.Error(s->range.start, std::string(rule.message), rule.subclause);
  if (s->rhs && ExprRefersToAutomatic(s->rhs, rule.names))
    diag.Error(s->range.start, std::string(rule.message), rule.subclause);
  // §13.3.1 for a task and §13.4.2 for a function each say the automatic items
  // cannot be accessed by hierarchical references, and neither names a position
  // the reference may stand in, so every position a statement holds a statement
  // in is one this report reaches. ForEachChildStmt in
  // elaborator_validate_internal.h states those positions once for the whole
  // elaborator.
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkStmtsForAutoRef(sub, rule, diag); });
}

static void CheckHierRefToAutomatic(const ModuleDecl* decl,
                                    const AutoSubroutineRule& rule,
                                    DiagEngine& diag) {
  if (rule.names.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      if (ExprRefersToAutomatic(item->assign_lhs, rule.names))
        diag.Error(item->loc, std::string(rule.message), rule.subclause);
      if (ExprRefersToAutomatic(item->assign_rhs, rule.names))
        diag.Error(item->loc, std::string(rule.message), rule.subclause);
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) WalkStmtsForAutoRef(item->body, rule, diag);
  }
}

void Elaborator::ValidateHierRefToAutomatic(const ModuleDecl* decl) {
  if (auto_task_func_names_.empty()) return;
  auto tasks = AutoSubroutineNames(decl, ModuleItemKind::kTaskDecl);
  CheckHierRefToAutomatic(
      decl,
      {tasks,
       "hierarchical reference to object in automatic task is not permitted",
       Subclause("13.3.1")},
      diag_);
  auto funcs = AutoSubroutineNames(decl, ModuleItemKind::kFunctionDecl);
  CheckHierRefToAutomatic(
      decl,
      {funcs,
       "hierarchical reference to object in automatic function is not "
       "permitted",
       Subclause("13.4.2")},
      diag_);
}

static bool IsProgramSubroutineCallExpr(
    const Expr* e, const std::unordered_set<std::string_view>& program_names) {
  if (!e || e->kind != ExprKind::kCall) return false;
  const Expr* callee = e->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return false;
  auto leftmost = HierRefLeftmost(callee);
  return !leftmost.empty() && program_names.count(leftmost) > 0;
}

static void WalkExprForProgramCall(
    const Expr* e, const std::unordered_set<std::string_view>& program_names,
    DiagEngine& diag, SourceLoc loc) {
  if (!e) return;
  if (IsProgramSubroutineCallExpr(e, program_names)) {
    diag.Error(loc,
               "calling a program subroutine from within a design module is "
               "not permitted",
               Subclause("24.5"));
  }
  WalkExprForProgramCall(e->lhs, program_names, diag, loc);
  WalkExprForProgramCall(e->rhs, program_names, diag, loc);
  WalkExprForProgramCall(e->condition, program_names, diag, loc);
  WalkExprForProgramCall(e->true_expr, program_names, diag, loc);
  WalkExprForProgramCall(e->false_expr, program_names, diag, loc);
  WalkExprForProgramCall(e->base, program_names, diag, loc);
  WalkExprForProgramCall(e->index, program_names, diag, loc);
  WalkExprForProgramCall(e->index_end, program_names, diag, loc);
  WalkExprForProgramCall(e->with_expr, program_names, diag, loc);
  WalkExprForProgramCall(e->repeat_count, program_names, diag, loc);
  for (auto* arg : e->args)
    WalkExprForProgramCall(arg, program_names, diag, loc);
  for (auto* elem : e->elements)
    WalkExprForProgramCall(elem, program_names, diag, loc);
}

static void WalkStmtForProgramCall(
    const Stmt* s, const std::unordered_set<std::string_view>& program_names,
    DiagEngine& diag) {
  if (!s) return;
  auto loc = s->range.start;
  WalkExprForProgramCall(s->lhs, program_names, diag, loc);
  WalkExprForProgramCall(s->rhs, program_names, diag, loc);
  WalkExprForProgramCall(s->expr, program_names, diag, loc);
  WalkExprForProgramCall(s->condition, program_names, diag, loc);
  // §24.5 says "Calling program subroutines from within design modules is
  // illegal and shall result in an error" and names no position the call is
  // allowed in, so every position a statement holds a statement in is one this
  // report reaches. ForEachChildStmt in elaborator_validate_internal.h states
  // those positions once for the whole elaborator.
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtForProgramCall(sub, program_names, diag);
  });
}

void Elaborator::ValidateProgramSubroutineCall(const ModuleDecl* decl) {
  if (program_inst_names_.empty()) return;
  if (decl->decl_kind == ModuleDeclKind::kProgram) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForProgramCall(item->assign_lhs, program_inst_names_, diag_,
                             item->loc);
      WalkExprForProgramCall(item->assign_rhs, program_inst_names_, diag_,
                             item->loc);
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body)
      WalkStmtForProgramCall(item->body, program_inst_names_, diag_);
  }
}

}  // namespace delta
