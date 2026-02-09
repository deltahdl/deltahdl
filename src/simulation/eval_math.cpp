#include <cmath>
#include <cstdint>
#include <random>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

namespace delta {

// ============================================================================
// Helpers
// ============================================================================

static double ArgToDouble(const Expr* arg, SimContext& ctx, Arena& arena) {
  auto val = EvalExpr(arg, ctx, arena);
  return static_cast<double>(val.ToUint64());
}

static Logic4Vec DoubleToResult(Arena& arena, double d) {
  auto v = static_cast<int64_t>(std::trunc(d));
  return MakeLogic4VecVal(arena, 64, static_cast<uint64_t>(v));
}

// ============================================================================
// section 20.8 -- Basic math functions
// ============================================================================

static Logic4Vec EvalLn(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  double x = ArgToDouble(expr->args[0], ctx, arena);
  return DoubleToResult(arena, std::log(x));
}

static Logic4Vec EvalLog10(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  double x = ArgToDouble(expr->args[0], ctx, arena);
  return DoubleToResult(arena, std::log10(x));
}

static Logic4Vec EvalExp(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  double x = ArgToDouble(expr->args[0], ctx, arena);
  return DoubleToResult(arena, std::exp(x));
}

static Logic4Vec EvalSqrt(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  double x = ArgToDouble(expr->args[0], ctx, arena);
  return DoubleToResult(arena, std::sqrt(x));
}

static Logic4Vec EvalPow(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 64, 0);
  double x = ArgToDouble(expr->args[0], ctx, arena);
  double y = ArgToDouble(expr->args[1], ctx, arena);
  return DoubleToResult(arena, std::pow(x, y));
}

static Logic4Vec EvalFloor(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  double x = ArgToDouble(expr->args[0], ctx, arena);
  return DoubleToResult(arena, std::floor(x));
}

static Logic4Vec EvalCeil(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  double x = ArgToDouble(expr->args[0], ctx, arena);
  return DoubleToResult(arena, std::ceil(x));
}

// ============================================================================
// section 20.8 -- Trigonometric functions
// ============================================================================

static Logic4Vec EvalSin(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  double x = ArgToDouble(expr->args[0], ctx, arena);
  return DoubleToResult(arena, std::sin(x));
}

static Logic4Vec EvalCos(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  double x = ArgToDouble(expr->args[0], ctx, arena);
  return DoubleToResult(arena, std::cos(x));
}

static Logic4Vec EvalTan(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  double x = ArgToDouble(expr->args[0], ctx, arena);
  return DoubleToResult(arena, std::tan(x));
}

static Logic4Vec EvalAsin(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  double x = ArgToDouble(expr->args[0], ctx, arena);
  return DoubleToResult(arena, std::asin(x));
}

static Logic4Vec EvalAcos(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  double x = ArgToDouble(expr->args[0], ctx, arena);
  return DoubleToResult(arena, std::acos(x));
}

static Logic4Vec EvalAtan(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  double x = ArgToDouble(expr->args[0], ctx, arena);
  return DoubleToResult(arena, std::atan(x));
}

static Logic4Vec EvalAtan2(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 64, 0);
  double y = ArgToDouble(expr->args[0], ctx, arena);
  double x = ArgToDouble(expr->args[1], ctx, arena);
  return DoubleToResult(arena, std::atan2(y, x));
}

// ============================================================================
// section 20.8 -- Hyperbolic functions
// ============================================================================

static Logic4Vec EvalHypot(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 64, 0);
  double x = ArgToDouble(expr->args[0], ctx, arena);
  double y = ArgToDouble(expr->args[1], ctx, arena);
  return DoubleToResult(arena, std::hypot(x, y));
}

static Logic4Vec EvalSinh(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  double x = ArgToDouble(expr->args[0], ctx, arena);
  return DoubleToResult(arena, std::sinh(x));
}

static Logic4Vec EvalCosh(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  double x = ArgToDouble(expr->args[0], ctx, arena);
  return DoubleToResult(arena, std::cosh(x));
}

static Logic4Vec EvalTanh(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  double x = ArgToDouble(expr->args[0], ctx, arena);
  return DoubleToResult(arena, std::tanh(x));
}

static Logic4Vec EvalAsinh(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  double x = ArgToDouble(expr->args[0], ctx, arena);
  return DoubleToResult(arena, std::asinh(x));
}

static Logic4Vec EvalAcosh(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  double x = ArgToDouble(expr->args[0], ctx, arena);
  return DoubleToResult(arena, std::acosh(x));
}

static Logic4Vec EvalAtanh(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  double x = ArgToDouble(expr->args[0], ctx, arena);
  return DoubleToResult(arena, std::atanh(x));
}

// ============================================================================
// section 20.14 -- Distribution functions
// ============================================================================

static Logic4Vec EvalDistUniform(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  // $dist_uniform(seed, lo, hi)
  if (expr->args.size() < 3) return MakeLogic4VecVal(arena, 32, 0);
  auto lo =
      static_cast<int32_t>(EvalExpr(expr->args[1], ctx, arena).ToUint64());
  auto hi =
      static_cast<int32_t>(EvalExpr(expr->args[2], ctx, arena).ToUint64());
  if (lo > hi) std::swap(lo, hi);
  int32_t range = hi - lo + 1;
  if (range <= 0) return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(lo));
  int32_t val = lo + static_cast<int32_t>(ctx.Urandom32() % range);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(val));
}

static Logic4Vec EvalDistNormal(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  // $dist_normal(seed, mean, std_dev)
  if (expr->args.size() < 3) return MakeLogic4VecVal(arena, 32, 0);
  auto mean =
      static_cast<int32_t>(EvalExpr(expr->args[1], ctx, arena).ToUint64());
  auto sdev =
      static_cast<int32_t>(EvalExpr(expr->args[2], ctx, arena).ToUint64());
  // Box-Muller approximation using urandom.
  double u1 = (ctx.Urandom32() + 1.0) / 4294967297.0;
  double u2 = (ctx.Urandom32() + 1.0) / 4294967297.0;
  double z = std::sqrt(-2.0 * std::log(u1)) * std::cos(2.0 * M_PI * u2);
  auto val = static_cast<int32_t>(mean + sdev * z);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(val));
}

static Logic4Vec EvalDistExponential(const Expr* expr, SimContext& ctx,
                                     Arena& arena) {
  // $dist_exponential(seed, mean)
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 32, 0);
  auto mean =
      static_cast<int32_t>(EvalExpr(expr->args[1], ctx, arena).ToUint64());
  double u = (ctx.Urandom32() + 1.0) / 4294967297.0;
  auto val = static_cast<int32_t>(-mean * std::log(u));
  if (val < 0) val = 0;
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(val));
}

static Logic4Vec EvalDistPoisson(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  // $dist_poisson(seed, mean)
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 32, 0);
  auto mean =
      static_cast<int32_t>(EvalExpr(expr->args[1], ctx, arena).ToUint64());
  double l_val = std::exp(-static_cast<double>(mean));
  int32_t k = 0;
  double p = 1.0;
  while (p > l_val && k < 1000) {
    ++k;
    double u = (ctx.Urandom32() + 1.0) / 4294967297.0;
    p *= u;
  }
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(k - 1));
}

static Logic4Vec EvalDistGeneric(const Expr* /*expr*/, SimContext& ctx,
                                 Arena& arena) {
  // $dist_chi_square, $dist_t, $dist_erlang -- simplified to urandom.
  return MakeLogic4VecVal(arena, 32, ctx.Urandom32());
}

// ============================================================================
// Category dispatchers
// ============================================================================

static Logic4Vec EvalBasicMath(const Expr* expr, SimContext& ctx, Arena& arena,
                               std::string_view name) {
  if (name == "$ln") return EvalLn(expr, ctx, arena);
  if (name == "$log10") return EvalLog10(expr, ctx, arena);
  if (name == "$exp") return EvalExp(expr, ctx, arena);
  if (name == "$sqrt") return EvalSqrt(expr, ctx, arena);
  if (name == "$pow") return EvalPow(expr, ctx, arena);
  if (name == "$floor") return EvalFloor(expr, ctx, arena);
  if (name == "$ceil") return EvalCeil(expr, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalTrigSysCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, std::string_view name) {
  if (name == "$sin") return EvalSin(expr, ctx, arena);
  if (name == "$cos") return EvalCos(expr, ctx, arena);
  if (name == "$tan") return EvalTan(expr, ctx, arena);
  if (name == "$asin") return EvalAsin(expr, ctx, arena);
  if (name == "$acos") return EvalAcos(expr, ctx, arena);
  if (name == "$atan") return EvalAtan(expr, ctx, arena);
  if (name == "$atan2") return EvalAtan2(expr, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalHyperbolicSysCall(const Expr* expr, SimContext& ctx,
                                       Arena& arena, std::string_view name) {
  if (name == "$hypot") return EvalHypot(expr, ctx, arena);
  if (name == "$sinh") return EvalSinh(expr, ctx, arena);
  if (name == "$cosh") return EvalCosh(expr, ctx, arena);
  if (name == "$tanh") return EvalTanh(expr, ctx, arena);
  if (name == "$asinh") return EvalAsinh(expr, ctx, arena);
  if (name == "$acosh") return EvalAcosh(expr, ctx, arena);
  if (name == "$atanh") return EvalAtanh(expr, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalDistSysCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, std::string_view name) {
  if (name == "$dist_uniform") return EvalDistUniform(expr, ctx, arena);
  if (name == "$dist_normal") return EvalDistNormal(expr, ctx, arena);
  if (name == "$dist_exponential") return EvalDistExponential(expr, ctx, arena);
  if (name == "$dist_poisson") return EvalDistPoisson(expr, ctx, arena);
  return EvalDistGeneric(expr, ctx, arena);
}

// ============================================================================
// Public dispatch: EvalMathSysCall
// ============================================================================

static bool IsBasicMathCall(std::string_view n) {
  return n == "$ln" || n == "$log10" || n == "$exp" || n == "$sqrt" ||
         n == "$pow" || n == "$floor" || n == "$ceil";
}

static bool IsTrigCall(std::string_view n) {
  return n == "$sin" || n == "$cos" || n == "$tan" || n == "$asin" ||
         n == "$acos" || n == "$atan" || n == "$atan2";
}

static bool IsHyperbolicCall(std::string_view n) {
  return n == "$hypot" || n == "$sinh" || n == "$cosh" || n == "$tanh" ||
         n == "$asinh" || n == "$acosh" || n == "$atanh";
}

Logic4Vec EvalMathSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                          std::string_view name) {
  if (IsBasicMathCall(name)) return EvalBasicMath(expr, ctx, arena, name);
  if (IsTrigCall(name)) return EvalTrigSysCall(expr, ctx, arena, name);
  if (IsHyperbolicCall(name))
    return EvalHyperbolicSysCall(expr, ctx, arena, name);
  if (name.starts_with("$dist_"))
    return EvalDistSysCall(expr, ctx, arena, name);
  return MakeLogic4VecVal(arena, 1, 0);
}

}  // namespace delta
