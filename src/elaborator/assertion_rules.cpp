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

bool IsAssertOrAssume(const Stmt* s) {
  return s->kind == StmtKind::kAssertImmediate ||
         s->kind == StmtKind::kAssumeImmediate;
}

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

void CheckClockAutomatics(
    const Stmt* s, const std::unordered_set<std::string_view>& automatics,
    DiagEngine& diag) {
  if (!EventsMention(s->assert_clock, automatics)) return;
  diag.Error(s->range.start,
             "a clocking event of a procedural concurrent assertion may not "
             "reference an automatic variable",
             Subclause("16.14.6"));
}

const std::vector<EventExpr>& DeclaredClock(const ModuleItem* decl) {
  return decl->kind == ModuleItemKind::kSequenceDecl ? decl->seq_clock
                                                     : decl->prop_clock;
}

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

bool ClockedOnAlone(const ModuleItem* decl, const EventExpr& block_clock) {
  const std::vector<EventExpr>& clock = DeclaredClock(decl);
  return decl->decl_clock_event_count <= 1 &&
         (clock.empty() ||
          (clock.size() == 1 && clock[0].edge == block_clock.edge &&
           SamePath(clock[0].signal, block_clock.signal)));
}

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

bool NegatesOrStrengthens(const PropertyExprNode* node) {
  using Kind = PropertyExprNode::Kind;
  if (node->kind == Kind::kNot) return true;
  return node->strong &&
         (node->kind == Kind::kNexttime || node->kind == Kind::kAlways ||
          node->kind == Kind::kEventually || node->kind == Kind::kUntil);
}

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
