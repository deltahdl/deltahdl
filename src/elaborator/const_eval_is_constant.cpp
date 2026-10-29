// §11.2.1 decides which expressions are constant expressions, and this file
// answers that question and nothing else. What such an expression is worth is
// folded in const_eval_func.cpp beside the §13.4.3 constant functions, and the
// two were one file until it reached the 1000-line maximum
// assert-no-oversized-source-files enforces.

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

      // §11.2.1's parenthetical names $timescale and $timeprecision, and §20.4,
      // which it points to, defines $timeunit and $timeprecision.
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
  // §20.6.2 and §20.7: $bits and an array query answer from the size of what
  // they are called on, so each is a constant expression only on an argument
  // whose size is fixed; $typename answers from its type.
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
  // A built-in method name that answers false here still falls through to the
  // compound lookup below, because a parameter of a class may carry one of
  // these names and `C.size` is then an ordinary scoped parameter read.
  auto builtin = BuiltinMethodCallIsConstant(expr, scope);
  if (builtin.value_or(false)) return true;
  // §8.25 sends a specialization's overrides to §23.10's rules, and §23.10.2
  // gives a parameter override a constant expression, so `C#(v)::P` is a
  // constant expression only where every override is one. The compound key
  // below is written by RecordClassParam from the class's own defaults, so
  // asking it alone would answer for `C#()::P` whatever the arguments were.
  // Parser::ParseParameterizedScope records the overrides in `elements` on
  // the scope's base and sets has_param_spec there, so that is what is read.
  if (expr->lhs->has_param_spec &&
      !AllElementsConstant(expr->lhs->elements, scope))
    return false;
  // §8.23: a chain of scope resolutions, `Outer::Inner::N`, is asked under
  // the key its class's registration records for the full path.
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
      // §6.20.7 lists the value assigned to a parameter among the contexts $
      // may appear in and gives `parameter r2 = $;` as its example, so $ is a
      // constant that names no declaration. Asking `scope` about it would
      // answer no, because nothing puts $ in a ScopeMap and nothing should.
      if (expr->text == "$") return true;
      // A.8.4 lists null among the constant primaries, and the parser keeps
      // the keyword as an identifier of that text, which no declaration bears.
      if (expr->text == "null") return true;
      return scope.count(expr->text) > 0;
    case ExprKind::kUnary:
      return IsConstantExpr(expr->lhs, scope);
    case ExprKind::kBinary:
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
    default:
      return false;
  }
}

}  // namespace delta
