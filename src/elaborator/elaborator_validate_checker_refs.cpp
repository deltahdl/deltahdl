// The checker rules that decide what a name inside or beside a checker may
// reach, split out of elaborator_validate_hier_refs.cpp, which is named for
// §23.6's hierarchical name and had reached the line cap holding the program
// rules beside these. §23.6 bars a hierarchical reference into a checker, and
// §17.7.1 bars a free checker variable from a continuous or blocking
// assignment and any checker variable from an assignment in an initial
// procedure.

#include <format>
#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

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

// §23.6 ends "Hierarchical references into checkers (see Clause 17) shall not
// be permitted", and §23.7 decides which dotted names are hierarchical at all:
// "the first component of the name matches a scope name while the first name
// component of a member select matches a data object or interface port name",
// settled by resolving that first component, after which "The name resolves to
// a data object or interface port. The dotted name shall be considered to be a
// select of that data object or interface port." §23.9 says which declaration
// the first component reaches -- "If it is declared locally, then the local
// item shall be used" -- and it lists a begin-end block among the scopes a
// declaration can be local to. So a name that merely spells a checker
// instance's identifier is a member select of the local, not a hierarchical
// reference into the checker, and this rule, which resolves nothing, reported
// one: a block-local `chk_inst` was refused for `chk_inst.a` wherever the
// module held a checker instance named `chk_inst`.
//
// The set is therefore taken by value and narrowed as the walk enters a scope,
// never widened on the way out -- the shape WalkStmtsForProgramRef below
// already uses for §24.3. What is erased is the declared name, because that is
// the component ExprRefersToChecker matches: HierRefLeftmost reduces
// `chk_inst.a` to `chk_inst`, so a declaration of `chk_inst` is what shadows it
// and a declaration of `a` is not. A block's declarations are erased before its
// statements are read, since a declaration and the use it shadows are siblings
// under the block rather than one inside the other.
//
// ExprRefersToChecker keeps the set by reference: an expression declares
// nothing, so the narrowing this walk has already done is the whole of what it
// needs, and it is passed the narrowed set from here.
static void WalkStmtsForCheckerRef(
    const Stmt* s, std::unordered_set<std::string_view> checker_names,
    DiagEngine& diag) {
  if (!s) return;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (sub != nullptr && sub->kind == StmtKind::kVarDecl)
      checker_names.erase(sub->var_name);
  });
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
//
// §23.9 decides which declaration the assignment target reaches -- "If it is
// declared locally, then the local item shall be used" -- and it lists a
// begin-end block among the scopes a declaration can be local to. So a
// block-local named after a free variable is what an assignment to that name
// updates, the free variable is not written at all, and this rule, which
// resolves nothing, refused one. The set is therefore taken by value and
// narrowed as the walk enters a scope, never widened on the way out, and the
// erase is keyed on the free variable's own name, because that is what
// HierRefLeftmost reduces the assignment target to.
//
// The narrowing runs below the checker body rather than at it.
// ValidateFreeCheckerVariableAssignments builds the set from the checker's own
// declarations, so a second declaration of one of those names in the checker
// body is the collision §23.9 forbids -- "An identifier shall be used to
// declare only one item within a scope" -- rather than a different variable an
// assignment could reach. Only a scope below the body can hold that other
// variable.
static void WalkStmtsForFreeBlockingAssign(
    const Stmt* s, std::unordered_set<std::string_view> free_vars,
    DiagEngine& diag) {
  if (!s) return;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (sub != nullptr && sub->kind == StmtKind::kVarDecl)
      free_vars.erase(sub->var_name);
  });
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

}  // namespace delta
