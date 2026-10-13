#include "elaborator/assertion_rules.h"

#include <format>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/assertion_walk.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/property_rewrite.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

namespace delta {

// §16.14.3: a cover statement may have an optional pass statement
// (statement_or_null), and that pass statement may hold no concurrent assert,
// assume or cover statement. A procedural concurrent assertion is parsed as an
// assert/assume/cover-immediate Stmt that carries is_procedural_concurrent;
// ordinary immediate assertions leave that flag clear and remain permitted.
// Returns the first offending statement, or nullptr when the pass statement
// contains none.
//
// §16.14.3 says the pass statement holds none and names no statement the
// prohibition is lifted in, so this descends every link ForEachChildStmt in
// elaborator_validate_internal.h names. It wrote out nine of the thirteen, so a
// concurrent assertion written in a randcase arm or a randsequence code block
// was not found and the cover statement holding it elaborated clean. Two of the
// four links it now reaches cannot hold one: A.6.8 admits in a
// for_initialization only a list_of_variable_assignments or a
// for_variable_declaration, and in a for_step only an operator_assignment, an
// inc_or_dec_expression or a function_subroutine_call, so no assertion
// statement stands in a for header. Descending them costs nothing and keeps the
// walk from naming any link itself.
//
// ForEachChildStmt gives the visitor no way to stop, so the first offending
// statement is kept in `hit` and the recursion runs only while `hit` is null.
// That is what makes this walk report the first one in source order rather than
// whichever link the list happens to visit last.
const Stmt* FindConcurrentAssertionInPassStmt(const Stmt* s) {
  if (s == nullptr) return nullptr;
  if (s->is_procedural_concurrent && (s->kind == StmtKind::kAssertImmediate ||
                                      s->kind == StmtKind::kAssumeImmediate ||
                                      s->kind == StmtKind::kCoverImmediate)) {
    return s;
  }
  const Stmt* hit = nullptr;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (hit) return;
    hit = FindConcurrentAssertionInPassStmt(sub);
  });
  return hit;
}

namespace {

// A procedural concurrent assertion's statement that is an assert or an
// assume rather than a cover.
bool IsAssertOrAssume(const Stmt* s) {
  return s->kind == StmtKind::kAssertImmediate ||
         s->kind == StmtKind::kAssumeImmediate;
}

// §16.14.1: the action block of a concurrent assert statement, and by §16.14.2
// of an assume statement, holds no concurrent assert, assume or cover
// statement, an immediate assertion being allowed there.
void CheckActionBlock(const Stmt* pass, const Stmt* fail, SourceLoc loc,
                      DiagEngine& diag) {
  const Stmt* nested = FindConcurrentAssertionInPassStmt(pass);
  if (nested == nullptr) nested = FindConcurrentAssertionInPassStmt(fail);
  if (nested == nullptr) return;
  diag.Error(loc,
             "the action block of a concurrent assert or assume statement may "
             "not include a concurrent assert, assume, or cover statement",
             Subclause("16.14.1"));
}

// §16.14.6: the clocking events of a procedural concurrent assertion name no
// automatic variable, though its other arguments may.
void CheckClockAutomatics(
    const Stmt* s, const std::unordered_set<std::string_view>& automatics,
    DiagEngine& diag) {
  if (!EventsMention(s->assert_clock, automatics)) return;
  diag.Error(s->range.start,
             "a clocking event of a procedural concurrent assertion may not "
             "reference an automatic variable",
             Subclause("16.14.6"));
}

// The clock a sequence or property declaration writes itself, empty where
// it writes none.
const std::vector<EventExpr>& DeclaredClock(const ModuleItem* decl) {
  return decl->kind == ModuleItemKind::kSequenceDecl ? decl->seq_clock
                                                     : decl->prop_clock;
}

// The declarations of `outside` the body of the sequence or property
// declaration `decl` instantiates, written as calls or as bare names.
std::vector<const ModuleItem*> InstancesInBody(const ModuleItem* decl,
                                               const NamedDecls& outside) {
  std::vector<const ModuleItem*> found;
  auto note = [&](const Expr* e) {
    ForEachSubExpr(e, [&](const Expr* sub) {
      const ModuleItem* named = InstantiatedDecl(sub, outside);
      if (named != nullptr) found.push_back(named);
    });
  };
  note(decl->prop_body_expr);
  ForEachTreeExpr(decl->prop_body_tree, note);
  ForEachBodyExpr(decl->seq_linear, note);
  return found;
}

// Whether the declaration `decl` is clocked on `block_clock` alone: written
// with that one event, or with none, so taking it.
bool ClockedOnAlone(const ModuleItem* decl, const EventExpr& block_clock) {
  const std::vector<EventExpr>& clock = DeclaredClock(decl);
  return decl->decl_clock_event_count <= 1 &&
         (clock.empty() ||
          (clock.size() == 1 && clock[0].edge == block_clock.edge &&
           SamePath(clock[0].signal, block_clock.signal)));
}

// §16.16 (b)(3): an instance, in a declaration of the clocking block `block`,
// of a named sequence or property declared outside it is singly clocked, on
// an event identical to the block's; one declared with no clock takes the
// block's. `outside` holds the declarations of the module by name.
void CheckClockingBlockInstances(const ModuleItem* block,
                                 const NamedDecls& outside, DiagEngine& diag) {
  if (block->clocking_event.size() != 1) return;
  const EventExpr& block_clock = block->clocking_event[0];
  for (const ModuleItem* inner : block->clocking_decls) {
    for (const ModuleItem* named : InstancesInBody(inner, outside)) {
      if (ClockedOnAlone(named, block_clock)) continue;
      diag.Error(inner->loc,
                 std::format("the instance of '{}' in clocking block '{}' is "
                             "not clocked on the block's clocking event alone",
                             named->name, block->name),
                 Subclause("16.16"));
    }
  }
}

// §16.12.17 Restriction 1: whether `node` is `not` or one of the strong
// operators s_nexttime, s_always, s_eventually, s_until and s_until_with,
// which no property expression instantiating a recursive property may stand
// under.
bool NegatesOrStrengthens(const PropertyExprNode* node) {
  using Kind = PropertyExprNode::Kind;
  if (node->kind == Kind::kNot) return true;
  return node->strong &&
         (node->kind == Kind::kNexttime || node->kind == Kind::kAlways ||
          node->kind == Kind::kEventually || node->kind == Kind::kUntil);
}

// §16.12.17 Restriction 1, for the property `node` of an assertion statement
// standing at `loc`: an instance of a property from which a recursive one is
// reachable may stand under no `not` or strong operator, so the negation of
// a recursive property is not asserted.
void CheckRecursiveUnderNegation(const PropertyExprNode* node, bool negated,
                                 SourceLoc loc,
                                 const PropertyRegistry& registry,
                                 DiagEngine& diag) {
  if (node == nullptr) return;
  if (negated && node->boolean != nullptr) {
    std::string name = InstanceDeclName(node->boolean);
    const ModuleItem* decl = registry.Find(name);
    if (decl != nullptr && decl->kind == ModuleItemKind::kPropertyDecl &&
        registry.ReachesRecursiveProperty(decl)) {
      diag.Error(loc,
                 "negation or strong operator applied to property \"" + name +
                     "\", which reaches a recursive property (Restriction 1)",
                 Subclause("16.12.17"));
    }
  }
  bool under = negated || NegatesOrStrengthens(node);
  for (const PropertyExprNode* operand : node->operands) {
    CheckRecursiveUnderNegation(operand, under, loc, registry, diag);
  }
}

// The checks on each concurrent assertion statement the procedure or
// subroutine `item` holds.
void CheckProceduralAssertions(const ModuleItem* item,
                               const PropertyRegistry& registry,
                               DiagEngine& diag) {
  std::unordered_set<std::string_view> automatics;
  bool collected = false;
  ForEachProceduralStmt(item, [&](const Stmt* s) {
    if (!s->is_procedural_concurrent) return;
    if (!collected) automatics = CollectItemAutomaticVarNames(item);
    collected = true;
    CheckClockAutomatics(s, automatics, diag);
    CheckRecursiveUnderNegation(s->assert_property, false, s->range.start,
                                registry, diag);
    if (IsAssertOrAssume(s)) {
      CheckActionBlock(s->assert_pass_stmt, s->assert_fail_stmt, s->range.start,
                       diag);
    }
  });
}

}  // namespace

void ValidateAssertionRules(const ModuleDecl* decl,
                            const PropertyRegistry& registry,
                            DiagEngine& diag) {
  const NamedDecls kDeclared = NamedDeclsByName(decl, true);
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kClockingBlock) {
      CheckClockingBlockInstances(item, kDeclared, diag);
    }
    if (item->kind == ModuleItemKind::kAssertProperty ||
        item->kind == ModuleItemKind::kAssumeProperty) {
      CheckActionBlock(item->assert_pass_stmt, item->assert_fail_stmt,
                       item->loc, diag);
    }
    if (item->body != nullptr && item->body->is_concurrent_clocked &&
        !IsProceduralItemKind(item->kind)) {
      CheckRecursiveUnderNegation(item->body->assert_property, false, item->loc,
                                  registry, diag);
    }
    CheckProceduralAssertions(item, registry, diag);
  }
}

}  // namespace delta
