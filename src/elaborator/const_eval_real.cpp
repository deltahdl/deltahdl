#include <cmath>
#include <cstdint>
#include <cstring>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/rtlir.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// The real-typed locals of the constant function call being folded, null
// outside every call (ConstFuncRealFrame).
std::unordered_map<std::string_view, double>* g_real_frame = nullptr;

}  // namespace

ConstFuncRealFrame::ConstFuncRealFrame() : prev_(g_real_frame) {
  g_real_frame = &values_;
}

ConstFuncRealFrame::~ConstFuncRealFrame() { g_real_frame = prev_; }

std::optional<double> ConstFuncRealLocal(std::string_view name) {
  if (g_real_frame == nullptr) return std::nullopt;
  auto it = g_real_frame->find(name);
  if (it == g_real_frame->end()) return std::nullopt;
  return it->second;
}

void SetConstFuncRealLocal(std::string_view name, double value) {
  (*g_real_frame)[name] = value;
}

void ClearConstFuncRealLocal(std::string_view name) {
  g_real_frame->erase(name);
}

bool IsConstFuncRealType(const DataType& type) {
  return type.kind == DataTypeKind::kReal ||
         type.kind == DataTypeKind::kShortreal ||
         type.kind == DataTypeKind::kRealtime;
}

// §11.3.1: the relational, equality and logical operators take real
// operands and give a 1-bit result.
static std::optional<bool> RealComparison(TokenKind op, double lhs,
                                          double rhs) {
  switch (op) {
    case TokenKind::kLt:
      return lhs < rhs;
    case TokenKind::kLtEq:
      return lhs <= rhs;
    case TokenKind::kGt:
      return lhs > rhs;
    case TokenKind::kGtEq:
      return lhs >= rhs;
    case TokenKind::kEqEq:
      return lhs == rhs;
    case TokenKind::kBangEq:
      return lhs != rhs;
    case TokenKind::kAmpAmp:
      return lhs != 0.0 && rhs != 0.0;
    case TokenKind::kPipePipe:
      return lhs != 0.0 || rhs != 0.0;
    default:
      return std::nullopt;
  }
}

// RealComparison's result read as the real it converts to, 1.0 or 0.0.
static std::optional<double> EvalRealComparison(TokenKind op, double lhs,
                                                double rhs) {
  std::optional<bool> result = RealComparison(op, lhs, rhs);
  if (!result) return std::nullopt;
  return static_cast<double>(*result);
}

static std::optional<double> EvalRealBinary(TokenKind op, double lhs,
                                            double rhs) {
  switch (op) {
    case TokenKind::kPlus:
      return lhs + rhs;
    case TokenKind::kMinus:
      return lhs - rhs;
    case TokenKind::kStar:
      return lhs * rhs;
    case TokenKind::kSlash:
      if (rhs == 0.0) return std::nullopt;
      return lhs / rhs;
    case TokenKind::kPower:
      return std::pow(lhs, rhs);
    default:
      return EvalRealComparison(op, lhs, rhs);
  }
}

static std::optional<double> EvalRealUnary(TokenKind op, double operand) {
  switch (op) {
    case TokenKind::kMinus:
      return -operand;
    case TokenKind::kPlus:
      return operand;
    case TokenKind::kBang:
      return operand == 0.0 ? 1.0 : 0.0;
    default:
      return std::nullopt;
  }
}

// The §20.5 real-returning conversions each take a single integral argument.
static std::optional<int64_t> ConstEvalFirstIntArg(const Expr* expr,
                                                   const ScopeMap& scope) {
  if (expr->args.empty()) return std::nullopt;
  return ConstEvalInt(expr->args[0], scope);
}

// §20.5: the real-returning conversion functions may appear in a constant real
// context. Each folds from the constant integral value of its argument.
// §20.8.2, Table 20-4: the real math functions, each the C function it
// corresponds to, by the number of arguments it takes.
using RealMathOne = double (*)(double);
using RealMathTwo = double (*)(double, double);

static const std::unordered_map<std::string_view, RealMathOne>&
RealMathOneArg() {
  static const std::unordered_map<std::string_view, RealMathOne> kFunctions = {
      {"$ln", [](double x) { return std::log(x); }},
      {"$log10", [](double x) { return std::log10(x); }},
      {"$exp", [](double x) { return std::exp(x); }},
      {"$sqrt", [](double x) { return std::sqrt(x); }},
      {"$floor", [](double x) { return std::floor(x); }},
      {"$ceil", [](double x) { return std::ceil(x); }},
      {"$sin", [](double x) { return std::sin(x); }},
      {"$cos", [](double x) { return std::cos(x); }},
      {"$tan", [](double x) { return std::tan(x); }},
      {"$asin", [](double x) { return std::asin(x); }},
      {"$acos", [](double x) { return std::acos(x); }},
      {"$atan", [](double x) { return std::atan(x); }},
      {"$sinh", [](double x) { return std::sinh(x); }},
      {"$cosh", [](double x) { return std::cosh(x); }},
      {"$tanh", [](double x) { return std::tanh(x); }},
      {"$asinh", [](double x) { return std::asinh(x); }},
      {"$acosh", [](double x) { return std::acosh(x); }},
      {"$atanh", [](double x) { return std::atanh(x); }},
  };
  return kFunctions;
}

static const std::unordered_map<std::string_view, RealMathTwo>&
RealMathTwoArgs() {
  static const std::unordered_map<std::string_view, RealMathTwo> kFunctions = {
      {"$pow", [](double x, double y) { return std::pow(x, y); }},
      {"$atan2", [](double y, double x) { return std::atan2(y, x); }},
      {"$hypot", [](double x, double y) { return std::hypot(x, y); }},
  };
  return kFunctions;
}

// §20.8.2: a real math function may be used in a constant expression, so it
// folds where each of its arguments, an integer one converted to real, does.
static std::optional<double> ConstEvalRealMathCall(const Expr* expr,
                                                   const ScopeMap& scope) {
  std::vector<double> args;
  for (const Expr* arg : expr->args) {
    std::optional<double> v = ConstEvalReal(arg, scope);
    if (!v) return std::nullopt;
    args.push_back(*v);
  }
  auto one = RealMathOneArg().find(expr->callee);
  if (one != RealMathOneArg().end() && args.size() == 1) {
    return one->second(args[0]);
  }
  auto two = RealMathTwoArgs().find(expr->callee);
  if (two != RealMathTwoArgs().end() && args.size() == 2) {
    return two->second(args[0], args[1]);
  }
  return std::nullopt;
}

static std::optional<double> ConstEvalRealSysCall(const Expr* expr,
                                                  const ScopeMap& scope) {
  if (expr->callee == "$itor") {
    auto iv = ConstEvalFirstIntArg(expr, scope);
    if (!iv) return std::nullopt;
    return static_cast<double>(*iv);
  }
  if (expr->callee == "$bitstoreal") {
    auto iv = ConstEvalFirstIntArg(expr, scope);
    if (!iv) return std::nullopt;
    auto bits = static_cast<uint64_t>(*iv);
    double d = 0.0;
    std::memcpy(&d, &bits, sizeof(d));
    return d;
  }
  if (expr->callee == "$bitstoshortreal") {
    auto iv = ConstEvalFirstIntArg(expr, scope);
    if (!iv) return std::nullopt;
    auto bits = static_cast<uint32_t>(*iv);
    float fv = 0.0F;
    std::memcpy(&fv, &bits, sizeof(fv));
    return static_cast<double>(fv);
  }
  return ConstEvalRealMathCall(expr, scope);
}

// §6.20.2 (printed pages 126-127): a name standing for a real parameter of
// the registered module is worth the double the elaborator resolved it to
// (RtlirParamDecl::resolved_real), which the ScopeMap, holding one integer
// per name, cannot carry: its slot for such a parameter holds the 0 the
// integer fold never wrote, so `parameter average_delay = (r + f) / 2` over
// `parameter r = 5.7` folded to 4.5 and `parameter twice = r1 * 2` over a
// declared `real r1` to 0. The registered parameter is consulted only where
// the scope holds its integer value or no value at all, as
// RegisteredParamValue (const_eval_bits.cpp) consults it, because a
// constant function's locals (§13.4.3) sit in the same map under bare names.
// Any other name is the integer the scope holds, widened.
static std::optional<double> ConstEvalRealIdentifier(const Expr* expr,
                                                     const ScopeMap& scope) {
  if (auto local = ConstFuncRealLocal(expr->text)) return local;
  auto it = scope.find(expr->text);
  const RtlirParamDecl* pd = RegisteredParamNamed(expr->text);
  if (pd != nullptr && pd->is_real_value &&
      (it == scope.end() || it->second == pd->resolved_value))
    return pd->resolved_real;
  if (it != scope.end()) return static_cast<double>(it->second);
  return std::nullopt;
}

std::optional<double> ConstEvalReal(const Expr* expr, const ScopeMap& scope) {
  if (!expr) return std::nullopt;

  switch (expr->kind) {
    case ExprKind::kRealLiteral:
    // §5.8: a time literal is interpreted as a realtime (real) value already
    // scaled to the current time unit; the parser folds that scaling into
    // real_val, so in a constant real context it evaluates exactly like any
    // other real literal.
    case ExprKind::kTimeLiteral:
      return expr->real_val;
    case ExprKind::kIntegerLiteral:
      return static_cast<double>(expr->int_val);
    case ExprKind::kIdentifier:
      return ConstEvalRealIdentifier(expr, scope);
    case ExprKind::kUnary: {
      auto operand = ConstEvalReal(expr->lhs, scope);
      if (!operand) return std::nullopt;
      return EvalRealUnary(expr->op, *operand);
    }
    case ExprKind::kBinary: {
      auto lhs = ConstEvalReal(expr->lhs, scope);
      auto rhs = ConstEvalReal(expr->rhs, scope);
      if (!lhs || !rhs) return std::nullopt;
      return EvalRealBinary(expr->op, *lhs, *rhs);
    }
    case ExprKind::kTernary: {
      auto cond = ConstFuncTruth(expr->condition, scope);
      if (!cond) return std::nullopt;
      return ConstEvalReal(*cond ? expr->true_expr : expr->false_expr, scope);
    }
    case ExprKind::kCall:
      // §13.4.3: a call of a constant function folds to the value it returns,
      // a real for one returning a real (ConstEvalUserCallReal).
      if (RegisteredConstFunc(expr) != nullptr)
        return ConstEvalUserCallReal(expr, scope);
      return ConstEvalRealSysCall(expr, scope);
    case ExprKind::kSystemCall:
      return ConstEvalRealSysCall(expr, scope);
    default:
      return std::nullopt;
  }
}

std::optional<double> ConstEvalReal(const Expr* expr) {
  static const ScopeMap kEmptyScope;
  return ConstEvalReal(expr, kEmptyScope);
}

}  // namespace delta
