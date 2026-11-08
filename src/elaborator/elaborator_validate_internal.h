#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/global_clocking_sampled_value.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

struct CompilationUnit;
struct RtlirModule;
struct TypeShapeTables;

using TypeMap = std::unordered_map<std::string_view, DataTypeKind>;
using NameSet = std::unordered_set<std::string_view>;

template <typename Rule, typename Visit>
void ForEachRandsequenceRuleStmt(Rule& rule, Visit visit) {
  for (auto& sub : rule.weight_code) visit(sub);
  for (auto& prod : rule.prods) {
    for (auto& sub : prod.code_stmts) visit(sub);
  }
}

template <typename S, typename Visit>
void ForEachRandsequenceStmt(S* s, Visit visit) {
  for (auto& production : s->rs_productions) {
    for (auto& rule : production.rules) {
      ForEachRandsequenceRuleStmt(rule, visit);
    }
  }
}

template <typename Visit>
void ForEachClassBodyItem(const ClassDecl* cls, Visit visit) {
  if (cls == nullptr) return;
  for (const auto* m : cls->members) {
    if (m == nullptr) continue;
    if (m->kind == ClassMemberKind::kMethod && m->method != nullptr) {
      visit(m->method);
    } else if (m->kind == ClassMemberKind::kClassDecl) {
      ForEachClassBodyItem(m->nested_class, visit);
    }
  }
}

template <typename Visit>
void ForEachBodyOwningItem(const std::vector<ModuleItem*>& items, Visit visit) {
  for (const auto* item : items) {
    if (item == nullptr) continue;
    if (item->kind == ModuleItemKind::kClassDecl) {
      ForEachClassBodyItem(item->class_decl, visit);
      continue;
    }
    visit(item);
  }
}

template <typename S, typename Visit>
void ForEachChildStmt(S* s, Visit visit) {
  for (auto& sub : s->stmts) visit(sub);
  for (auto& sub : s->fork_stmts) visit(sub);
  for (auto& sub : s->for_inits) visit(sub);
  for (auto& sub : s->for_steps) visit(sub);
  visit(s->then_branch);
  visit(s->else_branch);
  visit(s->body);
  visit(s->for_body);
  visit(s->assert_pass_stmt);
  visit(s->assert_fail_stmt);
  for (auto& ci : s->case_items) visit(ci.body);
  for (auto& rc : s->randcase_items) visit(rc.second);
  ForEachRandsequenceStmt(s, visit);
}

template <typename Visit>
void ForEachBlockLet(const Stmt* s, Visit visit) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kBlockItemDecl &&
      s->decl_item->kind == ModuleItemKind::kLetDecl)
    visit(s->decl_item);
  ForEachChildStmt(s,
                   [&visit](const Stmt* sub) { ForEachBlockLet(sub, visit); });
}

template <typename Visit>
void ForEachScopeLet(const std::vector<ModuleItem*>& items, Visit visit) {
  for (ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kLetDecl) visit(item);
  }
  ForEachBodyOwningItem(items, [&visit](const ModuleItem* owner) {
    for (const Stmt* s : owner->func_body_stmts) ForEachBlockLet(s, visit);
  });
}

template <typename Item, typename Visit>
void ForEachRandsequenceItemExpr(Item& item, Visit visit) {
  for (auto& arg : item.args) visit(arg);
}

template <typename Prod, typename Visit>
void ForEachRandsequenceProdExpr(Prod& prod, Visit visit) {
  visit(prod.condition);
  visit(prod.repeat_count);
  visit(prod.case_expr);
  ForEachRandsequenceItemExpr(prod.item, visit);
  ForEachRandsequenceItemExpr(prod.if_true, visit);
  ForEachRandsequenceItemExpr(prod.if_false, visit);
  ForEachRandsequenceItemExpr(prod.repeat_item, visit);
  for (auto& ci : prod.case_items) {
    for (auto& p : ci.patterns) visit(p);
    ForEachRandsequenceItemExpr(ci.item, visit);
  }
}

template <typename Rule, typename Visit>
void ForEachRandsequenceRuleExpr(Rule& rule, Visit visit) {
  visit(rule.weight);
  visit(rule.rand_join_expr);
  for (auto& item : rule.rand_join_items) {
    ForEachRandsequenceItemExpr(item, visit);
  }
  for (auto& prod : rule.prods) ForEachRandsequenceProdExpr(prod, visit);
}

template <typename S, typename Visit>
void ForEachRandsequenceExpr(S* s, Visit visit) {
  for (auto& production : s->rs_productions) {
    for (auto& rule : production.rules)
      ForEachRandsequenceRuleExpr(rule, visit);
  }
}

template <typename Prod, typename Visit>
void ForEachRandsequenceProdItem(Prod& prod, Visit visit) {
  visit(prod.item);
  visit(prod.if_true);
  visit(prod.if_false);
  visit(prod.repeat_item);
  for (auto& ci : prod.case_items) visit(ci.item);
}

template <typename Rule, typename Visit>
void ForEachRandsequenceRuleItem(Rule& rule, Visit visit) {
  for (auto& item : rule.rand_join_items) visit(item);
  for (auto& prod : rule.prods) ForEachRandsequenceProdItem(prod, visit);
}

template <typename S, typename Visit>
void ForEachRandsequenceItem(S* s, Visit visit) {
  for (auto& production : s->rs_productions) {
    for (auto& rule : production.rules)
      ForEachRandsequenceRuleItem(rule, visit);
  }
}

template <typename S, typename Visit>
void ForEachChildExpr(S* s, Visit visit) {
  visit(s->condition);
  visit(s->lhs);
  visit(s->rhs);
  visit(s->delay);
  visit(s->cycle_delay);
  visit(s->for_cond);
  visit(s->expr);
  visit(s->assert_expr);
  visit(s->repeat_event_count);
  visit(s->var_init);
  for (auto& ev : s->events) {
    visit(ev.signal);
    visit(ev.iff_condition);
  }
  for (auto& e : s->wait_order_events) visit(e);
  for (auto& rc : s->randcase_items) visit(rc.first);
  for (auto& ci : s->case_items) {
    for (auto& p : ci.patterns) visit(p);
  }
  for (auto& d : s->var_unpacked_dims) visit(d);
  ForEachRandsequenceExpr(s, visit);
}

template <typename Visit>
void ForEachPatternBinding(const Expr* p, Visit visit) {
  if (p == nullptr) return;
  if (p->kind == ExprKind::kBinary && p->op == TokenKind::kAmpAmpAmp) {
    ForEachPatternBinding(p->lhs, visit);
    return;
  }
  if (p->kind == ExprKind::kIdentifier && p->is_pattern_binding) {
    visit(p);
    return;
  }
  if (p->kind == ExprKind::kTagged) {
    ForEachPatternBinding(p->lhs, visit);
    return;
  }
  if (p->kind == ExprKind::kAssignmentPattern) {
    for (const Expr* e : p->elements) ForEachPatternBinding(e, visit);
  }
}

template <typename Fn>
bool AnyExprChild(const Expr* e, Fn&& fn) {
  for (const Expr* child : {e->lhs, e->rhs, e->condition, e->true_expr,
                            e->false_expr, e->base, e->index, e->index_end,
                            e->with_expr, e->stream_range, e->repeat_count}) {
    if (fn(child)) return true;
  }
  for (const Expr* child : e->args) {
    if (fn(child)) return true;
  }
  for (const Expr* child : e->elements) {
    if (fn(child)) return true;
  }
  for (const Expr* child : e->pattern_keys) {
    if (fn(child)) return true;
  }
  return false;
}

template <typename Vars>
bool NamesAVariable(const Expr* e, const Vars& vars) {
  if (e == nullptr || e->kind == ExprKind::kSystemCall) return false;
  if (e->kind == ExprKind::kIdentifier) return vars.count(e->text) != 0;
  return AnyExprChild(
      e, [&](const Expr* child) { return NamesAVariable(child, vars); });
}

template <typename Fn>
void ForEachExprChild(const Expr* e, Fn&& fn) {
  AnyExprChild(e, [&fn](const Expr* child) {
    fn(child);
    return false;
  });
}

template <typename Fn>
void ForEachExprUnder(const Expr* e, Fn& fn) {
  if (e == nullptr) return;
  fn(e);
  if (e->kind == ExprKind::kMemberAccess) {
    ForEachExprUnder(e->lhs, fn);
    return;
  }
  ForEachExprChild(e,
                   [&fn](const Expr* child) { ForEachExprUnder(child, fn); });
}

struct ProceduralRoot {
  const ModuleItem* item = nullptr;
  const Stmt* body = nullptr;
};

void CollectProceduralRoots(const std::vector<ModuleItem*>& items,
                            std::vector<ProceduralRoot>& out,
                            bool skip_defaulted = false);

std::vector<const ModuleDecl*> EnclosingDecls(const CompilationUnit* unit,
                                              const ModuleDecl* decl);

std::optional<int64_t> ComputeDimSize(const Expr* dim);

int ResolveActualArgIndex(const Expr* expr, size_t formal_index,
                          std::string_view formal_name,
                          size_t positional_count);

std::unordered_set<std::string_view> UnpackedStructVars(
    const ModuleDecl* decl, const TypedefMap& typedefs);

struct ArrayPatternCheck {
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& aggregate_typedefs;
  const std::unordered_map<std::string_view, DataTypeKind>& var_types;
  DiagEngine& diag;

  void Check(const Expr* pattern, const DataType& elem_type,
             const std::vector<Expr*>& dims, SourceLoc loc) const;
  void CheckSized(const Expr* pattern, const DataType& elem_type,
                  std::span<const uint32_t> unpacked_sizes,
                  SourceLoc loc) const;
};
void CheckArrayPatternIndexKeys(const ArrayPatternCheck& check,
                                const Expr* pattern, SourceLoc loc);
std::optional<std::string> ArrayPatternKeyIdentity(const Expr* key);
std::string_view LhsBaseName(const Expr* e);
const Expr* PatternReplication(const Expr* pattern);
std::optional<int64_t> PositionalItemCount(const Expr* pattern);

struct StructPatternTarget {
  const TypedefMap& typedefs;
  SourceLoc loc;
  DiagEngine& diag;
};
const std::vector<StructMember>* StructMembersOf(const DataType& type,
                                                 const TypedefMap& typedefs);
void CheckStructPattern(const Expr* pattern,
                        const std::vector<StructMember>& members,
                        const StructPatternTarget& target);
std::optional<int64_t> FoldPackedStructPattern(const Expr* pattern,
                                               const DataType& type,
                                               const TypedefMap& typedefs,
                                               const ScopeMap& scope);
void CheckStructPatternFor(const Expr* value, const DataType* target_type,
                           const StructPatternTarget& target);
inline std::string_view HierRefLeftmost(const Expr* e) {
  if (e == nullptr) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  if (e->kind == ExprKind::kMemberAccess && e->lhs)
    return HierRefLeftmost(e->lhs);
  return {};
}

bool IsRealValued(
    const Expr* e,
    const std::unordered_map<std::string_view, DataTypeKind>& var_types);
bool ExprContainsIdent(const Expr* e, std::string_view name);
bool ExprUsesInterconnect(const Expr* e,
                          const std::unordered_set<std::string_view>& names);
void CheckPcontDynamicArrayTarget(
    const Stmt* s, const std::unordered_set<std::string_view>& dyn_names,
    DiagEngine& diag);
void CollectProcTargets(const std::vector<FunctionArg>& formals,
                        const std::vector<Stmt*>& body,
                        std::unordered_map<std::string_view, SourceLoc>& out);
void CollectProcContAssignTargets(
    const std::vector<FunctionArg>& formals, const std::vector<Stmt*>& body,
    std::unordered_map<std::string_view, SourceLoc>& out);
std::span<Expr* const> PrimitiveOutputTerminals(const ModuleItem* item);
void ReportProcContAssignNets(
    const std::vector<FunctionArg>& formals, const std::vector<Stmt*>& body,
    const std::unordered_set<std::string_view>& net_names, DiagEngine& diag);

void CollectForceReleaseTargets(
    const Stmt* s, std::unordered_map<std::string_view, SourceLoc>& out);
void CheckInterconnectProcContAssign(
    const Stmt* s,
    const std::unordered_set<std::string_view>& interconnect_names,
    DiagEngine& diag);
void CheckInterconnectProceduralRead(
    const Stmt* s,
    const std::unordered_set<std::string_view>& interconnect_names,
    DiagEngine& diag);
void CheckProceduralAssignLhs(const Stmt* s, DiagEngine& diag);
void CheckHighzStrengthPair(const ModuleItem* item, DiagEngine& diag);
void ReportForceOverMixture(std::string_view name, SourceLoc loc,
                            DiagEngine& diag);
using SelectShapeMap = std::unordered_map<std::string_view, VarSelectShape>;

struct SelectOperands {
  const NameSet& variables;
  const NameSet& parameters;
  const SelectShapeMap& shapes;
};

void CheckRealSelect(const Expr* e, const TypeMap& types,
                     const SelectOperands& operands, DiagEngine& diag);
void CheckScalarSelect(const Expr* e, const NameSet& scalars, DiagEngine& diag);
void CheckIndexedPartSelectWidth(const Expr* e, const ScopeMap& scope,
                                 DiagEngine& diag);
void CheckScalarSelectStmt(const Stmt* s, const NameSet& scalars,
                           DiagEngine& diag);
void CheckRealSelectStmt(const Stmt* s, const TypeMap& types,
                         const SelectOperands& operands, DiagEngine& diag);
void CheckIndexedPartSelectWidthStmt(const Stmt* s, const ScopeMap& scope,
                                     DiagEngine& diag);

using GclkKindPredicate = bool (*)(GlobalClockingSampledFunction);
const Expr* FindGclkFunctionRefInItem(const ModuleItem* item,
                                      GclkKindPredicate match,
                                      bool include_property_slot);

bool IsArrayQueryFunc(std::string_view callee);
bool IsArrayBuiltinMethodName(std::string_view name);
void ForEachItemAndGenerateDescendant(
    const ModuleItem* item, const std::function<void(const ModuleItem*)>& fn);
bool TypedefHasDynamicDim(const std::vector<Expr*>& dims);

struct NbaDynamicTables {
  const TypeShapeTables& shape;
  const CompilationUnit* unit;
};
void CheckNbaDynamicElements(const ModuleDecl* decl,
                             const NbaDynamicTables& tables, DiagEngine& diag);

void ReportPackageSubroutineStaticInits(const PackageDecl* pkg,
                                        DiagEngine& diag);

void CheckIsunboundedArgs(const ModuleDecl* decl, const RtlirModule* mod,
                          DiagEngine& diag);

void CheckTimeformatArgs(const ModuleDecl* decl, DiagEngine& diag);

class BodyDeclScopes {
 public:
  struct Decl {
    std::string_view name;
    const DataType* type = nullptr;
    const std::vector<Expr*>* unpacked_dims = nullptr;
    bool automatic = false;
  };

  explicit BodyDeclScopes(bool default_auto) : default_auto_(default_auto) {}

  void DeclareFormal(const FunctionArg& arg);

  const Decl* Find(std::string_view name) const;

  void Walk(const Stmt* s, const std::function<void(const Stmt*)>& visit);

 private:
  bool default_auto_;
  std::vector<Decl> decls_;
};

std::string CallName(const Expr* call);

std::string EnabledSubroutineName(const Stmt* s);

void ReportNonEventOperands(const ModuleDecl* decl, const TypeMap& kinds,
                            DiagEngine& diag);

bool ReturnsAValue(const ModuleItem* subroutine);

void WarnDiscardedReturn(SourceLoc loc, std::string_view callee,
                         std::string_view remedy, DiagEngine& diag);

void ValidateGenerateValueParams(const ModuleItem* item, const RtlirModule* mod,
                                 const ScopeMap& scope, DiagEngine& diag);

void ValidateUnitClassCallArgs(const CompilationUnit& unit, DiagEngine& diag);

}  // namespace delta
