#include <algorithm>
#include <cstddef>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/elaborator_validate_operations.h"
#include "elaborator/net_data_type.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

static bool IsBlockDeclared(
    const std::vector<std::pair<std::string_view, bool>>& decls,
    std::string_view name) {
  return std::ranges::any_of(
      decls, [name](const auto& decl) { return decl.first == name; });
}

void ElaboratorOperationRules::WalkStmtsForProceduralArrayPattern(
    const Stmt* s) {
  if (s == nullptr) return;
  const ArrayPatternCheck kCheck{typedefs_, aggregate_typedef_names_,
                                 var_types_, diag_};
  bool is_assign = s->kind == StmtKind::kBlockingAssign ||
                   s->kind == StmtKind::kNonblockingAssign;
  if (is_assign && s->lhs->kind == ExprKind::kIdentifier &&
      !IsBlockDeclared(block_decls_, s->lhs->text)) {
    auto it = pattern_target_arrays_.find(s->lhs->text);
    if (it != pattern_target_arrays_.end()) {
      kCheck.Check(s->rhs, it->second->data_type, it->second->unpacked_dims,
                   s->rhs->range.start);
    }
  }
  if (s->kind == StmtKind::kVarDecl && s->var_init != nullptr) {
    kCheck.Check(s->var_init, s->var_decl_type, s->var_unpacked_dims,
                 s->var_init->range.start);
  }
  size_t mark = block_decls_.size();
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForProceduralArrayPattern(sub); });
  block_decls_.resize(mark);
  if (s->kind == StmtKind::kVarDecl)
    block_decls_.emplace_back(s->var_name, !s->var_unpacked_dims.empty());
}

namespace {
struct TypedPatternScope {
  const ArrayPatternCheck& check;
  const TypedefMap& typedefs;
  const std::unordered_map<std::string_view, std::vector<Expr*>>& td_array_dims;
  const std::unordered_map<std::string_view, const ModuleItem*>& module_vars;
  const BodyDeclScopes* body;
};

struct PrefixArrayType {
  const DataType* elem;
  std::vector<Expr*> unpacked_dims;
};
}  // namespace

static std::optional<PrefixArrayType> TypedefPrefixType(
    std::string_view name, const TypedPatternScope& scope) {
  DataType named;
  named.kind = DataTypeKind::kNamed;
  named.type_name = name;
  std::vector<std::string_view> chain;
  if (FollowTypedefs(named, scope.typedefs, chain) == nullptr)
    return std::nullopt;
  for (std::string_view link : chain) {
    auto dims = scope.td_array_dims.find(link);
    if (dims != scope.td_array_dims.end())
      return PrefixArrayType{&scope.typedefs.find(link)->second, dims->second};
  }
  return PrefixArrayType{&scope.typedefs.find(name)->second, {}};
}

static std::optional<PrefixArrayType> TypeRefExprType(
    const Expr* ref, const TypedPatternScope& scope) {
  std::string_view name = ExprIdent(ref->lhs);
  if (scope.body != nullptr) {
    if (const BodyDeclScopes::Decl* decl = scope.body->Find(name))
      return PrefixArrayType{decl->type, *decl->unpacked_dims};
  }
  auto it = scope.module_vars.find(name);
  if (it == scope.module_vars.end()) return std::nullopt;
  return PrefixArrayType{&it->second->data_type, it->second->unpacked_dims};
}

static std::string ScopedTypedefKey(const Expr* scoped) {
  return std::string(ExprIdent(scoped->lhs)) +
         "::" + std::string(ExprIdent(scoped->rhs));
}

static std::optional<PrefixArrayType> TypeValuePrefixType(
    const DataType* written, const TypedPatternScope& scope) {
  if (written->kind == DataTypeKind::kNamed &&
      written->packed_dim_left == nullptr && written->scope_name.empty())
    return TypedefPrefixType(written->type_name, scope);
  return PrefixArrayType{written, {}};
}

static std::optional<PrefixArrayType> PrefixType(
    const Expr* cast, const TypedPatternScope& scope) {
  const Expr* ref = cast->rhs;
  if (ref == nullptr) return TypedefPrefixType(cast->text, scope);
  if (ref->kind != ExprKind::kTypeRef)
    return TypedefPrefixType(ScopedTypedefKey(ref), scope);
  if (ref->type_value != nullptr)
    return TypeValuePrefixType(ref->type_value, scope);
  if (ref->lhs->is_scope_resolution)
    return TypedefPrefixType(ScopedTypedefKey(ref->lhs), scope);
  return TypeRefExprType(ref, scope);
}

static void CheckTypedArrayPatternsIn(const Expr* e,
                                      const TypedPatternScope& scope) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kCast &&
      e->lhs->kind == ExprKind::kAssignmentPattern) {
    if (auto type = PrefixType(e, scope)) {
      scope.check.Check(e->lhs, *type->elem, type->unpacked_dims,
                        e->range.start);
    }
  }
  ForEachExprChild(e, [&scope](const Expr* child) {
    CheckTypedArrayPatternsIn(child, scope);
  });
}

static void CheckProceduralTypedArrayPatterns(
    const std::vector<FunctionArg>& formals, const std::vector<Stmt*>& body,
    TypedPatternScope scope) {
  BodyDeclScopes decls(false);
  for (const auto& arg : formals) decls.DeclareFormal(arg);
  scope.body = &decls;
  for (const Stmt* s : body) {
    decls.Walk(s, [&scope](const Stmt* st) {
      ForEachChildExpr(
          st, [&scope](const Expr* e) { CheckTypedArrayPatternsIn(e, scope); });
    });
  }
}

static void CheckItemTypedArrayPatterns(const ModuleItem* item,
                                        const TypedPatternScope& scope) {
  CheckTypedArrayPatternsIn(item->init_expr, scope);
  CheckTypedArrayPatternsIn(item->assign_lhs, scope);
  CheckTypedArrayPatternsIn(item->assign_rhs, scope);
  for (const auto& conn : item->inst_ports)
    CheckTypedArrayPatternsIn(conn.second, scope);
  if (IsProceduralItemKind(item->kind))
    CheckProceduralTypedArrayPatterns({}, {item->body}, scope);
  CheckProceduralTypedArrayPatterns(item->func_args, item->func_body_stmts,
                                    scope);
}

using StructTargetTypes = std::unordered_map<std::string_view, const DataType*>;

static const DataType* WholeTargetType(const Expr* lhs,
                                       const BodyDeclScopes& scopes,
                                       const StructTargetTypes& module_types) {
  if (lhs->kind != ExprKind::kIdentifier) return nullptr;
  if (const BodyDeclScopes::Decl* decl = scopes.Find(lhs->text))
    return decl->unpacked_dims->empty() ? decl->type : nullptr;
  auto it = module_types.find(lhs->text);
  return it == module_types.end() ? nullptr : it->second;
}

static void CheckProceduralStructPatterns(
    const std::vector<FunctionArg>& formals, const std::vector<Stmt*>& body,
    const StructTargetTypes& module_types, const TypedefMap& typedefs,
    DiagEngine& diag) {
  BodyDeclScopes scopes(false);
  for (const auto& arg : formals) scopes.DeclareFormal(arg);
  for (const Stmt* s : body) {
    scopes.Walk(s, [&](const Stmt* st) {
      if (st->kind == StmtKind::kVarDecl && st->var_init != nullptr &&
          st->var_unpacked_dims.empty()) {
        CheckStructPatternFor(st->var_init, &st->var_decl_type,
                              {typedefs, st->var_init->range.start, diag});
      }
      if (st->kind != StmtKind::kBlockingAssign &&
          st->kind != StmtKind::kNonblockingAssign)
        return;
      CheckStructPatternFor(st->rhs,
                            WholeTargetType(st->lhs, scopes, module_types),
                            {typedefs, st->rhs->range.start, diag});
    });
  }
}

static void CheckItemStructPatterns(const ModuleItem* item,
                                    const StructTargetTypes& targets,
                                    const TypedefMap& typedefs,
                                    DiagEngine& diag) {
  if (IsProceduralItemKind(item->kind))
    CheckProceduralStructPatterns({}, {item->body}, targets, typedefs, diag);
  CheckProceduralStructPatterns(item->func_args, item->func_body_stmts, targets,
                                typedefs, diag);
  if (item->kind != ModuleItemKind::kContAssign) return;
  const BodyDeclScopes kNoLocals(false);
  CheckStructPatternFor(item->assign_rhs,
                        WholeTargetType(item->assign_lhs, kNoLocals, targets),
                        {typedefs, item->assign_rhs->range.start, diag});
}

void ElaboratorOperationRules::CheckContinuousArrayPattern(
    const ModuleItem* item) {
  const ArrayPatternCheck kCheck{typedefs_, aggregate_typedef_names_,
                                 var_types_, diag_};
  if (item->kind == ModuleItemKind::kNetDecl && item->init_expr != nullptr) {
    kCheck.Check(item->init_expr, item->data_type, item->unpacked_dims,
                 item->init_expr->range.start);
  }
  if (item->kind != ModuleItemKind::kContAssign ||
      item->assign_lhs->kind != ExprKind::kIdentifier)
    return;
  auto it = pattern_target_arrays_.find(item->assign_lhs->text);
  if (it == pattern_target_arrays_.end()) return;
  kCheck.Check(item->assign_rhs, it->second->data_type,
               it->second->unpacked_dims, item->assign_rhs->range.start);
}

void ElaboratorOperationRules::ValidateProceduralArrayPatterns(
    const ModuleDecl* decl) {
  pattern_target_arrays_.clear();
  StructTargetTypes struct_targets;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kNetDecl)
      pattern_target_arrays_[item->name] = item;
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    pattern_target_arrays_[item->name] = item;
    if (item->unpacked_dims.empty())
      struct_targets[item->name] = &item->data_type;
  }
  const ArrayPatternCheck kCheck{typedefs_, aggregate_typedef_names_,
                                 var_types_, diag_};
  const TypedPatternScope kTypedScope{kCheck, typedefs_, td_array_dims_,
                                      pattern_target_arrays_, nullptr};
  for (const auto& param : decl->params)
    CheckTypedArrayPatternsIn(param.second, kTypedScope);
  for (const auto* item : decl->items) {
    CheckContinuousArrayPattern(item);
    CheckItemTypedArrayPatterns(item, kTypedScope);
    if (IsProceduralItemKind(item->kind))
      WalkStmtsForProceduralArrayPattern(item->body);
    CheckItemStructPatterns(item, struct_targets, typedefs_, diag_);
    for (const auto& arg : item->func_args)
      block_decls_.emplace_back(arg.name, !arg.unpacked_dims.empty());
    for (const auto* s : item->func_body_stmts)
      WalkStmtsForProceduralArrayPattern(s);
    block_decls_.clear();
  }
}

}  // namespace delta
