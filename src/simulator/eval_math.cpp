#include <cmath>
#include <cstdint>
#include <cstring>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/probabilistic_distribution.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

namespace delta {

static double ArgToDouble(const Expr* arg, SimContext& ctx, Arena& arena) {
  if (arg->kind == ExprKind::kRealLiteral) return arg->real_val;
  auto val = EvalExpr(arg, ctx, arena);
  if (val.is_real) return RealVecToDouble(val);
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

static double RefUniform(int32_t* seed, int32_t start, int32_t end) {
  const double kD = 0.00000011920928955078125;
  double a = 0.0, b = 0.0;
  if (*seed == 0) *seed = 259341593;
  if (start >= end) {
    a = 0.0;
    b = 2147483647.0;
  } else {
    a = static_cast<double>(start);
    b = static_cast<double>(end);
  }
  *seed = static_cast<int32_t>(69069u * static_cast<uint32_t>(*seed) + 1u);
  uint32_t bits = (static_cast<uint32_t>(*seed) >> 9) | 0x3f800000u;
  float fs = 0.0F;
  std::memcpy(&fs, &bits, sizeof(fs));
  auto c = static_cast<double>(fs);
  c = c + (c * kD);
  c = ((b - a) * (c - 1.0)) + a;
  return c;
}

static double RefNormal(int32_t* seed, int32_t mean, int32_t deviation) {
  double v1 = 0.0, v2 = 0.0, s = 1.0;
  while (s >= 1.0 || s == 0.0) {
    v1 = RefUniform(seed, -1, 1);
    v2 = RefUniform(seed, -1, 1);
    s = v1 * v1 + v2 * v2;
  }
  s = v1 * std::sqrt(-2.0 * std::log(s) / s);
  return s * static_cast<double>(deviation) + static_cast<double>(mean);
}

static double RefExponential(int32_t* seed, int32_t mean) {
  double n = RefUniform(seed, 0, 1);
  if (n != 0) n = -std::log(n) * mean;
  return n;
}

static int32_t RefPoisson(int32_t* seed, int32_t mean) {
  int32_t n = 0;
  double q = -static_cast<double>(mean);
  double p = std::exp(q);
  q = RefUniform(seed, 0, 1);
  while (p < q) {
    n++;
    q = RefUniform(seed, 0, 1) * q;
  }
  return n;
}

static double RefChiSquare(int32_t* seed, int32_t deg_of_free) {
  double x = 0.0;
  if (deg_of_free % 2) {
    x = RefNormal(seed, 0, 1);
    x = x * x;
  } else {
    x = 0.0;
  }
  for (int32_t k = 2; k <= deg_of_free; k += 2) {
    x = x + 2 * RefExponential(seed, 1);
  }
  return x;
}

static double RefT(int32_t* seed, int32_t deg_of_free) {
  double chi2 = RefChiSquare(seed, deg_of_free);
  double div = chi2 / static_cast<double>(deg_of_free);
  double root = std::sqrt(div);
  return RefNormal(seed, 0, 1) / root;
}

static double RefErlangian(int32_t* seed, int32_t k, int32_t mean) {
  double x = 1.0;
  for (int32_t i = 1; i <= k; i++) x = x * RefUniform(seed, 0, 1);
  auto a = static_cast<double>(mean);
  auto b = static_cast<double>(k);
  return -a * std::log(x) / b;
}

int32_t RtlDistRound(double r) {
  if (r >= 0) return static_cast<int32_t>(r + 0.5);
  r = -r;
  return -static_cast<int32_t>(r + 0.5);
}

static int32_t FloorDistDraw(double r) {
  return r >= 0 ? static_cast<int32_t>(r) : static_cast<int32_t>(r - 1);
}

static int32_t RtlDistUniformGeneral(int32_t* seed, int32_t start,
                                     int32_t end) {
  end++;
  double r = RefUniform(seed, start, end);
  int32_t i = FloorDistDraw(r);
  if (i < start) i = start;
  if (i >= end) i = end - 1;
  return i;
}

static int32_t RtlDistUniformHighEdge(int32_t* seed, int32_t start,
                                      int32_t end) {
  start--;
  double r = RefUniform(seed, start, end) + 1.0;
  int32_t i = FloorDistDraw(r);
  if (i <= start) i = start + 1;
  if (i > end) i = end;
  return i;
}

static int32_t RtlDistUniformFullRange(int32_t* seed, int32_t start,
                                       int32_t end) {
  double r = (RefUniform(seed, start, end) + 2147483648.0) / 4294967295.0;
  r = r * 4294967296.0 - 2147483648.0;
  return FloorDistDraw(r);
}

int32_t RtlDistUniform(int32_t* seed, int32_t start, int32_t end) {
  if (start >= end) return start;
  if (end != INT32_MAX) return RtlDistUniformGeneral(seed, start, end);
  if (start != INT32_MIN) return RtlDistUniformHighEdge(seed, start, end);
  return RtlDistUniformFullRange(seed, start, end);
}

int32_t RtlDistNormal(int32_t* seed, int32_t mean, int32_t sd) {
  return RtlDistRound(RefNormal(seed, mean, sd));
}
int32_t RtlDistExponential(int32_t* seed, int32_t mean) {
  if (mean <= 0) return 0;
  return RtlDistRound(RefExponential(seed, mean));
}
int32_t RtlDistPoisson(int32_t* seed, int32_t mean) {
  if (mean <= 0) return 0;
  return RefPoisson(seed, mean);
}
int32_t RtlDistChiSquare(int32_t* seed, int32_t df) {
  if (df <= 0) return 0;
  return RtlDistRound(RefChiSquare(seed, df));
}
int32_t RtlDistT(int32_t* seed, int32_t df) {
  if (df <= 0) return 0;
  return RtlDistRound(RefT(seed, df));
}
int32_t RtlDistErlang(int32_t* seed, int32_t k, int32_t mean) {
  if (k <= 0) return 0;
  return RtlDistRound(RefErlangian(seed, k, mean));
}

void WriteBackDistributionSeed(const Expr* seed_arg, int32_t seed,
                               SimContext& ctx, Arena& arena) {
  if (seed_arg->kind != ExprKind::kIdentifier &&
      seed_arg->kind != ExprKind::kMemberAccess &&
      seed_arg->kind != ExprKind::kSelect) {
    return;
  }
  PerformBlockingAssign(
      seed_arg, MakeLogic4VecVal(arena, 32, static_cast<uint32_t>(seed)), ctx,
      arena);
}

static void RequirePositiveDistArg(const Expr* arg, SimContext& ctx,
                                   Arena& arena, std::string_view what) {
  auto v = static_cast<int32_t>(EvalExpr(arg, ctx, arena).ToUint64());
  if (v <= 0) {
    ctx.GetDiag().Warning(
        arg->range.start,
        std::string(what) +
            " argument of a distribution function shall be greater than 0",
        Subclause("20.14.2"));
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
  ValidateDistArgs(expr, ctx, arena, name);

  auto arg = [&](size_t i) -> int32_t {
    if (i >= expr->args.size()) return 0;
    return static_cast<int32_t>(EvalExpr(expr->args[i], ctx, arena).ToUint64());
  };
  int32_t seed = arg(0);

  int32_t result = 0;
  if (name == "$dist_uniform") {
    result = RtlDistUniform(&seed, arg(1), arg(2));
  } else if (name == "$dist_normal") {
    result = RtlDistNormal(&seed, arg(1), arg(2));
  } else if (name == "$dist_exponential") {
    result = RtlDistExponential(&seed, arg(1));
  } else if (name == "$dist_poisson") {
    result = RtlDistPoisson(&seed, arg(1));
  } else if (name == "$dist_chi_square") {
    result = RtlDistChiSquare(&seed, arg(1));
  } else if (name == "$dist_t") {
    result = RtlDistT(&seed, arg(1));
  } else if (name == "$dist_erlang") {
    result = RtlDistErlang(&seed, arg(1), arg(2));
  }

  WriteBackDistributionSeed(expr->args[0], seed, ctx, arena);
  Logic4Vec out = MakeLogic4VecVal(
      arena, 32, static_cast<uint64_t>(static_cast<uint32_t>(result)));
  out.is_signed = true;
  return out;
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

}  // namespace delta
