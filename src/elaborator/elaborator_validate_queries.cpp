#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/system_call_writes.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

void CheckPlaOutputOperand(
    const Expr* e, const std::unordered_set<std::string_view>& net_names,
    SourceLoc loc, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kConcatenation) {
    for (auto* el : e->elements)
      CheckPlaOutputOperand(el, net_names, loc, diag);
    return;
  }
  auto base = LhsBaseName(e);
  if (!base.empty() && net_names.count(base) != 0) {
    diag.Error(loc,
               "a PLA modeling system task writes its output terms, so each "
               "must be a variable, not a net",
               Subclause("20.16"));
  }
}

void CheckPlaOutputTermsExpr(
    const Expr* e, const std::unordered_set<std::string_view>& net_names,
    DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSystemCall && IsPlaSystemTask(e->callee) &&
      e->args.size() >= 3 && e->args[2]) {
    CheckPlaOutputOperand(e->args[2], net_names, e->range.start, diag);
  }
  CheckPlaOutputTermsExpr(e->lhs, net_names, diag);
  CheckPlaOutputTermsExpr(e->rhs, net_names, diag);
  CheckPlaOutputTermsExpr(e->condition, net_names, diag);
  CheckPlaOutputTermsExpr(e->true_expr, net_names, diag);
  CheckPlaOutputTermsExpr(e->false_expr, net_names, diag);
  CheckPlaOutputTermsExpr(e->base, net_names, diag);
  CheckPlaOutputTermsExpr(e->index, net_names, diag);
  for (auto* a : e->args) CheckPlaOutputTermsExpr(a, net_names, diag);
  for (auto* el : e->elements) CheckPlaOutputTermsExpr(el, net_names, diag);
}

void CheckPlaOutputTermsStmt(
    const Stmt* s, const std::unordered_set<std::string_view>& net_names,
    DiagEngine& diag) {
  if (!s) return;
  CheckPlaOutputTermsExpr(s->condition, net_names, diag);
  CheckPlaOutputTermsExpr(s->lhs, net_names, diag);
  CheckPlaOutputTermsExpr(s->rhs, net_names, diag);
  CheckPlaOutputTermsExpr(s->expr, net_names, diag);
  CheckPlaOutputTermsExpr(s->var_init, net_names, diag);
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckPlaOutputTermsStmt(sub, net_names, diag);
  });
}

bool IsStringOutputTask(std::string_view callee) {
  return callee == "$swrite" || callee == "$swriteb" || callee == "$swriteh" ||
         callee == "$swriteo" || callee == "$sformat";
}

void CheckStringOutputTarget(const Expr* e, const TypeMap& types,
                             DiagEngine& diag) {
  if (e == nullptr || e->args.empty() || e->args[0] == nullptr) return;
  auto base = LhsBaseName(e->args[0]);
  if (base.empty()) return;
  auto it = types.find(base);
  if (it != types.end() && IsRealType(it->second)) {
    diag.Error(e->range.start,
               "$swrite/$sformat cannot write its text into a real "
               "variable; give it an integral, string or unpacked byte "
               "array target",
               Subclause("21.3.3"));
  }
}

void CheckStringOutputTargetsExpr(const Expr* e, const TypeMap& types,
                                  DiagEngine& diag) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kSystemCall && IsStringOutputTask(e->callee))
    CheckStringOutputTarget(e, types, diag);
  CheckStringOutputTargetsExpr(e->lhs, types, diag);
  CheckStringOutputTargetsExpr(e->rhs, types, diag);
  CheckStringOutputTargetsExpr(e->condition, types, diag);
  CheckStringOutputTargetsExpr(e->true_expr, types, diag);
  CheckStringOutputTargetsExpr(e->false_expr, types, diag);
  CheckStringOutputTargetsExpr(e->base, types, diag);
  CheckStringOutputTargetsExpr(e->index, types, diag);
  for (auto* a : e->args) CheckStringOutputTargetsExpr(a, types, diag);
  for (auto* el : e->elements) CheckStringOutputTargetsExpr(el, types, diag);
}

void CheckStringOutputTargetsStmt(const Stmt* s, const TypeMap& types,
                                  DiagEngine& diag) {
  if (s == nullptr) return;
  CheckStringOutputTargetsExpr(s->condition, types, diag);
  CheckStringOutputTargetsExpr(s->lhs, types, diag);
  CheckStringOutputTargetsExpr(s->rhs, types, diag);
  CheckStringOutputTargetsExpr(s->expr, types, diag);
  CheckStringOutputTargetsExpr(s->var_init, types, diag);
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckStringOutputTargetsStmt(sub, types, diag);
  });
}

}  // namespace

void Elaborator::ValidateStringOutputTaskTargets(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->body) CheckStringOutputTargetsStmt(item->body, var_types_, diag_);
    for (auto* s : item->func_body_stmts)
      CheckStringOutputTargetsStmt(s, var_types_, diag_);
    CheckStringOutputTargetsExpr(item->init_expr, var_types_, diag_);
  }
}

namespace {

bool IsBitVectorFunction(std::string_view callee) {
  return callee == "$countbits" || callee == "$countones" ||
         callee == "$onehot" || callee == "$onehot0" || callee == "$isunknown";
}

static bool NamesAMember(const Expr* e) {
  while (e) {
    if (e->kind == ExprKind::kMemberAccess) return true;
    if (e->kind != ExprKind::kSelect) return false;
    e = e->base;
  }
  return false;
}

void CheckBitVectorFunctionArg(const Expr* call, const TypeMap& types,
                               DiagEngine& diag) {
  if (call->callee == "$countbits" && call->args.size() < 2) {
    diag.Error(call->range.start,
               "'$countbits' requires at least one control_bit argument",
               Subclause("20.9"));
    return;
  }
  if (call->args.empty() || call->args[0] == nullptr) return;
  if (NamesAMember(call->args[0])) return;
  auto base = LhsBaseName(call->args[0]);
  if (base.empty()) return;
  auto it = types.find(base);
  if (it == types.end()) return;
  auto k = it->second;
  if (IsRealType(k) || k == DataTypeKind::kEvent ||
      k == DataTypeKind::kChandle || k == DataTypeKind::kVirtualInterface) {
    diag.Error(
        call->range.start,
        std::format("'{}' works on bit-stream values, and its expression "
                    "argument's type is not a bit-stream type",
                    call->callee),
        Subclause("20.9"));
  }
}

void CheckBitVectorArgExpr(const Expr* e, const TypeMap& types,
                           DiagEngine& diag) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kSystemCall && IsBitVectorFunction(e->callee))
    CheckBitVectorFunctionArg(e, types, diag);
  CheckBitVectorArgExpr(e->lhs, types, diag);
  CheckBitVectorArgExpr(e->rhs, types, diag);
  CheckBitVectorArgExpr(e->condition, types, diag);
  CheckBitVectorArgExpr(e->true_expr, types, diag);
  CheckBitVectorArgExpr(e->false_expr, types, diag);
  CheckBitVectorArgExpr(e->base, types, diag);
  CheckBitVectorArgExpr(e->index, types, diag);
  for (auto* a : e->args) CheckBitVectorArgExpr(a, types, diag);
  for (auto* el : e->elements) CheckBitVectorArgExpr(el, types, diag);
}

void CheckBitVectorArgStmt(const Stmt* s, const TypeMap& types,
                           DiagEngine& diag) {
  if (s == nullptr) return;
  CheckBitVectorArgExpr(s->condition, types, diag);
  CheckBitVectorArgExpr(s->lhs, types, diag);
  CheckBitVectorArgExpr(s->rhs, types, diag);
  CheckBitVectorArgExpr(s->expr, types, diag);
  CheckBitVectorArgExpr(s->var_init, types, diag);
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckBitVectorArgStmt(sub, types, diag); });
}

}  // namespace

void Elaborator::ValidateBitVectorFunctionArgs(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->body) CheckBitVectorArgStmt(item->body, var_types_, diag_);
    for (auto* s : item->func_body_stmts)
      CheckBitVectorArgStmt(s, var_types_, diag_);
    CheckBitVectorArgExpr(item->init_expr, var_types_, diag_);
    CheckBitVectorArgExpr(item->assign_rhs, var_types_, diag_);
  }
}

void Elaborator::ValidatePlaOutputTerms(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->body) CheckPlaOutputTermsStmt(item->body, net_names_, diag_);
    for (auto* s : item->func_body_stmts)
      CheckPlaOutputTermsStmt(s, net_names_, diag_);
    CheckPlaOutputTermsExpr(item->init_expr, net_names_, diag_);
  }
}

namespace {

struct PlaDeclRanges {
  std::optional<int64_t> packed_left;
  std::optional<int64_t> packed_right;
  std::vector<std::pair<int64_t, int64_t>> unpacked;
};

using PlaRangeMap = std::unordered_map<std::string_view, PlaDeclRanges>;

void CheckPlaArgAscending(const Expr* arg, const PlaRangeMap& ranges,
                          bool check_unpacked, const char* message,
                          DiagEngine& diag) {
  if (!arg) return;
  if (arg->kind == ExprKind::kSelect && arg->index && !arg->index_end &&
      !arg->is_part_select_plus && !arg->is_part_select_minus) {
    return;
  }
  auto base = LhsBaseName(arg);
  if (base.empty()) return;
  auto it = ranges.find(base);
  if (it == ranges.end()) return;
  const PlaDeclRanges& r = it->second;
  if (r.packed_left && r.packed_right && *r.packed_left > *r.packed_right) {
    diag.Error(arg->range.start, message, Subclause("20.16.3"));
    return;
  }
  if (check_unpacked) {
    for (const auto& dim : r.unpacked) {
      if (dim.first > dim.second) {
        diag.Error(arg->range.start, message, Subclause("20.16.3"));
        return;
      }
    }
  }
}

void CheckPlaAscendingExpr(const Expr* e, const PlaRangeMap& ranges,
                           DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSystemCall && IsPlaSystemTask(e->callee)) {
    if (e->args.size() >= 1)
      CheckPlaArgAscending(e->args[0], ranges, true,
                           "the memory of a PLA modeling system task has a "
                           "descending range; give it an ascending one",
                           diag);
    if (e->args.size() >= 2)
      CheckPlaArgAscending(e->args[1], ranges, false,
                           "the input terms of a PLA modeling system task have "
                           "a descending range; give them an ascending one",
                           diag);
    if (e->args.size() >= 3)
      CheckPlaArgAscending(
          e->args[2], ranges, false,
          "the output terms of a PLA modeling system task have a descending "
          "range; give them an ascending one",
          diag);
  }
  CheckPlaAscendingExpr(e->lhs, ranges, diag);
  CheckPlaAscendingExpr(e->rhs, ranges, diag);
  CheckPlaAscendingExpr(e->condition, ranges, diag);
  CheckPlaAscendingExpr(e->true_expr, ranges, diag);
  CheckPlaAscendingExpr(e->false_expr, ranges, diag);
  CheckPlaAscendingExpr(e->base, ranges, diag);
  CheckPlaAscendingExpr(e->index, ranges, diag);
  for (auto* a : e->args) CheckPlaAscendingExpr(a, ranges, diag);
  for (auto* el : e->elements) CheckPlaAscendingExpr(el, ranges, diag);
}

void CheckPlaAscendingStmt(const Stmt* s, const PlaRangeMap& ranges,
                           DiagEngine& diag) {
  if (!s) return;
  CheckPlaAscendingExpr(s->condition, ranges, diag);
  CheckPlaAscendingExpr(s->lhs, ranges, diag);
  CheckPlaAscendingExpr(s->rhs, ranges, diag);
  CheckPlaAscendingExpr(s->expr, ranges, diag);
  CheckPlaAscendingExpr(s->var_init, ranges, diag);
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckPlaAscendingStmt(sub, ranges, diag); });
}

PlaDeclRanges CollectPlaDeclRanges(const ModuleItem* item,
                                   const ScopeMap& scope) {
  PlaDeclRanges r;
  r.packed_left = ConstEvalInt(item->data_type.packed_dim_left, scope);
  r.packed_right = ConstEvalInt(item->data_type.packed_dim_right, scope);
  for (auto* dim : item->unpacked_dims) {
    if (dim && dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
      auto l = ConstEvalInt(dim->lhs, scope);
      auto rr = ConstEvalInt(dim->rhs, scope);
      if (l && rr) r.unpacked.push_back({*l, *rr});
    }
  }
  return r;
}

}  // namespace

void Elaborator::ValidatePlaAscendingOrder(const ModuleDecl* decl) {
  PlaRangeMap ranges;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kVarDecl &&
        item->kind != ModuleItemKind::kNetDecl)
      continue;
    ranges.emplace(item->name,
                   CollectPlaDeclRanges(item, pla_ascending_scope_));
  }
  if (ranges.empty()) return;
  for (const auto* item : decl->items) {
    if (item->body) CheckPlaAscendingStmt(item->body, ranges, diag_);
    for (auto* s : item->func_body_stmts)
      CheckPlaAscendingStmt(s, ranges, diag_);
    CheckPlaAscendingExpr(item->init_expr, ranges, diag_);
  }
}

namespace {

bool DimIsVariableSized(const Expr* d) {
  if (d == nullptr) return true;
  return d->kind == ExprKind::kIdentifier && (d->text == "$" || d->text == "*");
}

using VarDimMap =
    std::unordered_map<std::string_view, const std::vector<Expr*>*>;

bool QueriesOneDimension(std::string_view callee) {
  return callee == "$left" || callee == "$right" || callee == "$low" ||
         callee == "$high" || callee == "$increment" || callee == "$size";
}

void CheckQueryOnStringIndex(const Expr* e, const VarDimMap& vars,
                             const ScopeMap& scope, DiagEngine& diag) {
  if (!QueriesOneDimension(e->callee)) return;
  auto it = vars.find(e->args[0]->text);
  if (it == vars.end()) return;
  std::optional<int64_t> n =
      e->args.size() >= 2 ? ConstEvalInt(e->args[1], scope) : 1;
  const std::vector<Expr*>& dims = *it->second;
  if (!n || *n < 1 || static_cast<uint64_t>(*n) > dims.size()) return;
  const Expr* dim = dims[static_cast<size_t>(*n - 1)];
  if (dim == nullptr || dim->kind != ExprKind::kIdentifier ||
      dim->text != "string") {
    return;
  }
  diag.Error(e->range.start,
             std::format("array query function '{}' cannot be used on the "
                         "associative dimension of '{}', whose index type "
                         "'string' has no integral values",
                         e->callee, e->args[0]->text),
             Subclause("20.7"));
}

void CheckQueryOnVariableSizedDim(const Expr* e, const VarDimMap& vars,
                                  const ScopeMap& scope, DiagEngine& diag) {
  if (e->args.size() < 2 || e->args[1] == nullptr) return;
  auto n_val = ConstEvalInt(e->args[1], scope);
  auto it = vars.find(e->args[0]->text);
  if (!n_val || *n_val <= 1 || it == vars.end()) return;
  auto n = static_cast<uint64_t>(*n_val);
  const std::vector<Expr*>& dims = *it->second;
  if (n <= dims.size() && DimIsVariableSized(dims[n - 1])) {
    diag.Error(e->range.start,
               std::format("array query function '{}' cannot query "
                           "variable-sized dimension {} of array '{}'",
                           e->callee, n, e->args[0]->text),
               Subclause("20.7.1"));
  }
}

void CheckArrayQueryOnVarDimExpr(const Expr* e, const VarDimMap& vars,
                                 const ScopeMap& scope, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSystemCall && IsArrayQueryFunc(e->callee) &&
      !e->args.empty() && e->args[0] &&
      e->args[0]->kind == ExprKind::kIdentifier) {
    CheckQueryOnStringIndex(e, vars, scope, diag);
    CheckQueryOnVariableSizedDim(e, vars, scope, diag);
  }
  CheckArrayQueryOnVarDimExpr(e->lhs, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(e->rhs, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(e->condition, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(e->true_expr, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(e->false_expr, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(e->base, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(e->index, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(e->index_end, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(e->repeat_count, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(e->with_expr, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(e->stream_range, vars, scope, diag);
  for (auto* a : e->args) CheckArrayQueryOnVarDimExpr(a, vars, scope, diag);
  for (auto* el : e->elements)
    CheckArrayQueryOnVarDimExpr(el, vars, scope, diag);
}

void CheckArrayQueryOnVarDimStmt(const Stmt* s, const VarDimMap& vars,
                                 const ScopeMap& scope, DiagEngine& diag) {
  if (!s) return;
  CheckArrayQueryOnVarDimExpr(s->condition, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(s->lhs, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(s->rhs, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(s->expr, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(s->delay, vars, scope, diag);
  CheckArrayQueryOnVarDimExpr(s->var_init, vars, scope, diag);
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckArrayQueryOnVarDimStmt(sub, vars, scope, diag);
  });
}

}  // namespace

void Elaborator::ValidateArrayQueryOnVariableDim(const ModuleDecl* decl) {
  VarDimMap vars;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && !item->unpacked_dims.empty())
      vars.emplace(item->name, &item->unpacked_dims);
  }
  if (vars.empty()) return;
  const ScopeMap& scope = array_query_dim_scope_;
  for (const auto* item : decl->items) {
    if (item->body) CheckArrayQueryOnVarDimStmt(item->body, vars, scope, diag_);
    for (auto* s : item->func_body_stmts)
      CheckArrayQueryOnVarDimStmt(s, vars, scope, diag_);
    CheckArrayQueryOnVarDimExpr(item->init_expr, vars, scope, diag_);
  }
}

}  // namespace delta
