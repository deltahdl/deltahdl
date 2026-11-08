#include <optional>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "parser/ast_expr.h"

namespace delta {

bool IsConstantSysFunc(std::string_view name) {
  static const std::unordered_set<std::string_view> kConstSysFuncs = {
      "$clog2",
      "$bits",
      "$countones",
      "$onehot",
      "$onehot0",
      "$isunknown",
      "$isunbounded",

      "$timescale",
      "$timeunit",
      "$timeprecision",

      "$itor",
      "$rtoi",
      "$bitstoreal",
      "$realtobits",
      "$bitstoshortreal",
      "$shortrealtobits",
      "$signed",
      "$unsigned",

      "$ln",
      "$log10",
      "$exp",
      "$sqrt",
      "$pow",
      "$floor",
      "$ceil",
      "$sin",
      "$cos",
      "$tan",
      "$asin",
      "$acos",
      "$atan",
      "$atan2",
      "$hypot",
      "$sinh",
      "$cosh",
      "$tanh",
      "$asinh",
      "$acosh",
      "$atanh",

      "$dimensions",
      "$unpacked_dimensions",
      "$left",
      "$right",
      "$low",
      "$high",
      "$increment",
      "$size",

      "$countbits",

      "$sformatf",
      "$typename",
  };
  return kConstSysFuncs.count(name) > 0;
}

bool AllElementsConstant(const std::vector<Expr*>& elems,
                         const ScopeMap& scope) {
  for (auto* elem : elems) {
    if (!IsConstantExpr(elem, scope)) return false;
  }
  return true;
}

static bool IsConstEvenWithNonConstArgs(std::string_view name) {
  static const std::unordered_set<std::string_view> kFuncs = {
      "$bits", "$dimensions", "$unpacked_dimensions", "$left", "$right",
      "$low",  "$high",       "$increment",           "$size", "$typename",
  };
  return kFuncs.count(name) > 0;
}

bool IsConstantWhateverItsArguments(const Expr* call) {
  if (!IsConstEvenWithNonConstArgs(call->callee)) return false;
  return call->callee == "$typename" || call->args.empty() ||
         !IsDynamicallySized(call->args[0]);
}

static bool IsConstantSysCallExpr(const Expr* expr, const ScopeMap& scope) {
  if (!IsConstantSysFunc(expr->callee)) return false;
  if (IsConstEvenWithNonConstArgs(expr->callee)) {
    return IsConstantWhateverItsArguments(expr);
  }
  return AllElementsConstant(expr->args, scope);
}

static bool IsConstantSelectExpr(const Expr* expr, const ScopeMap& scope) {
  if (!IsConstantExpr(expr->base, scope)) return false;
  if (!IsConstantExpr(expr->index, scope)) return false;
  if (expr->index_end && !IsConstantExpr(expr->index_end, scope)) return false;
  return true;
}

static bool IsConstantMemberAccessExpr(const Expr* expr,
                                       const ScopeMap& scope) {
  auto builtin = BuiltinMethodCallIsConstant(expr, scope);
  if (builtin.value_or(false)) return true;
  if (expr->lhs->has_param_spec &&
      !AllElementsConstant(expr->lhs->elements, scope))
    return false;
  if (!builtin && !expr->is_scope_resolution &&
      IsConstantExpr(expr->lhs, scope))
    return true;
  std::optional<std::string> key = ScopedNameKey(expr);
  return key && scope.count(*key) > 0;
}

bool IsConstantExpr(const Expr* expr, const ScopeMap& scope) {
  if (!expr) return false;

  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kStringLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
    case ExprKind::kTimeLiteral:
      return true;
    case ExprKind::kIdentifier:
      if (expr->text == "$") return true;
      if (expr->text == "null") return true;
      return scope.count(expr->text) > 0;
    case ExprKind::kUnary:
      return IsConstantExpr(expr->lhs, scope);
    case ExprKind::kBinary:
      if (IsTypeRefComparison(expr)) return true;
      return IsConstantExpr(expr->lhs, scope) &&
             IsConstantExpr(expr->rhs, scope);
    case ExprKind::kTernary:
      return IsConstantExpr(expr->condition, scope) &&
             IsConstantExpr(expr->true_expr, scope) &&
             IsConstantExpr(expr->false_expr, scope);
    case ExprKind::kConcatenation:
      return AllElementsConstant(expr->elements, scope);
    case ExprKind::kReplicate:
      return IsConstantExpr(expr->repeat_count, scope) &&
             AllElementsConstant(expr->elements, scope);
    case ExprKind::kSelect:
      return IsConstantSelectExpr(expr, scope);
    case ExprKind::kSystemCall:
      return IsConstantSysCallExpr(expr, scope);
    case ExprKind::kCast:
      return IsConstantExpr(expr->lhs, scope);
    case ExprKind::kAssignmentPattern:
      return AllElementsConstant(expr->elements, scope);
    case ExprKind::kCall:
      if (auto builtin = BuiltinMethodCallIsConstant(expr, scope))
        return *builtin;
      if (auto let = LetCallIsConstant(expr, scope)) return *let;
      return AllElementsConstant(expr->args, scope);
    case ExprKind::kMemberAccess:
      return IsConstantMemberAccessExpr(expr, scope);
    case ExprKind::kMinTypMax:
      return IsConstantExpr(expr->lhs, scope) &&
             IsConstantExpr(expr->condition, scope) &&
             IsConstantExpr(expr->rhs, scope);
    default:
      return false;
  }
}

}  // namespace delta
