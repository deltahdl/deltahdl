#include <cmath>
#include <cstdint>
#include <cstring>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

static double ArgToDouble(const Expr* arg, SimContext& ctx, Arena& arena) {
  if (arg->kind == ExprKind::kRealLiteral) return arg->real_val;
  auto val = EvalExpr(arg, ctx, arena);
  if (arg->kind == ExprKind::kIdentifier && ctx.IsRealVariable(arg->text)) {
    uint64_t bits = val.ToUint64();
    double d = 0.0;
    std::memcpy(&d, &bits, sizeof(double));
    return d;
  }
  return static_cast<double>(val.ToUint64());
}

static Logic4Vec DoubleToResult(Arena& arena, double d) {
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  auto vec = MakeLogic4VecVal(arena, 64, bits);
  vec.is_real = true;
  return vec;
}

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

static Logic4Vec EvalDistUniform(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {

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

  if (expr->args.size() < 3) return MakeLogic4VecVal(arena, 32, 0);
  auto mean =
      static_cast<int32_t>(EvalExpr(expr->args[1], ctx, arena).ToUint64());
  auto sdev =
      static_cast<int32_t>(EvalExpr(expr->args[2], ctx, arena).ToUint64());

  double u1 = (ctx.Urandom32() + 1.0) / 4294967297.0;
  double u2 = (ctx.Urandom32() + 1.0) / 4294967297.0;
  double z = std::sqrt(-2.0 * std::log(u1)) * std::cos(2.0 * M_PI * u2);
  auto val = static_cast<int32_t>(mean + sdev * z);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(val));
}

static Logic4Vec EvalDistExponential(const Expr* expr, SimContext& ctx,
                                     Arena& arena) {

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

static Logic4Vec EvalDistGeneric(const Expr* , SimContext& ctx,
                                 Arena& arena) {

  return MakeLogic4VecVal(arena, 32, ctx.Urandom32());
}

// §20.14.2: the leading argument of every distribution function is an inout
// seed. Reseeding the active generator from the caller's seed before drawing
// makes the function repeatable — the same seed always yields the same value —
// the way $random (§20.14.1) uses a seed to select a stream.
static void SeedDistFromArg(const Expr* seed_arg, SimContext& ctx,
                            Arena& arena) {
  ctx.SeedUrandom(
      static_cast<uint32_t>(EvalExpr(seed_arg, ctx, arena).ToUint64()));
}

// §20.14.2: the seed is an inout argument — a value goes in and a different
// value comes back. When the seed names a variable it is advanced to the
// generator's next state so consecutive calls walk the stream, while a run that
// re-initializes the seed to its original value replays identically.
static void AdvanceDistSeed(const Expr* seed_arg, SimContext& ctx,
                            Arena& arena) {
  if (seed_arg->kind != ExprKind::kIdentifier) return;
  Variable* var = ctx.FindVariable(seed_arg->text);
  if (var == nullptr) return;
  uint32_t next = ctx.Urandom32();
  var->value = MakeLogic4VecVal(arena, var->value.width, next);
}

// §20.14.2: mean, degree_of_freedom, and k_stage shall be greater than 0 for the
// distributions that consume them. A non-positive value leaves the distribution
// undefined, so it is reported; the draw still proceeds.
static void RequirePositiveDistArg(const Expr* arg, SimContext& ctx,
                                   Arena& arena, std::string_view what) {
  auto v = static_cast<int32_t>(EvalExpr(arg, ctx, arena).ToUint64());
  if (v <= 0) {
    ctx.GetDiag().Warning(
        {}, std::string(what) +
                " argument of a distribution function shall be greater than 0");
  }
}

static void ValidateDistArgs(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::string_view name) {
  const auto& args = expr->args;
  if (name == "$dist_erlang") {
    if (args.size() > 1) RequirePositiveDistArg(args[1], ctx, arena, "k_stage");
    if (args.size() > 2) RequirePositiveDistArg(args[2], ctx, arena, "mean");
    return;
  }
  // The positivity requirement covers exponential, poisson, chi-square, t, and
  // erlang — not $dist_normal, whose mean may take any value.
  if (args.size() <= 1) return;
  if (name == "$dist_exponential" || name == "$dist_poisson") {
    RequirePositiveDistArg(args[1], ctx, arena, "mean");
  } else if (name == "$dist_chi_square" || name == "$dist_t") {
    RequirePositiveDistArg(args[1], ctx, arena, "degree_of_freedom");
  }
}

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
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  // Reseed from the inout seed (args[0]) so the function is repeatable, then
  // check the arguments the distribution requires to be positive.
  SeedDistFromArg(expr->args[0], ctx, arena);
  ValidateDistArgs(expr, ctx, arena, name);

  Logic4Vec result;
  if (name == "$dist_uniform") {
    result = EvalDistUniform(expr, ctx, arena);
  } else if (name == "$dist_normal") {
    result = EvalDistNormal(expr, ctx, arena);
  } else if (name == "$dist_exponential") {
    result = EvalDistExponential(expr, ctx, arena);
  } else if (name == "$dist_poisson") {
    result = EvalDistPoisson(expr, ctx, arena);
  } else {
    result = EvalDistGeneric(expr, ctx, arena);
  }

  // The seed is inout: hand back a different value so the next call advances.
  AdvanceDistSeed(expr->args[0], ctx, arena);
  return result;
}

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

}
