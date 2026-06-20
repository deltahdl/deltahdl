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

// ---------------------------------------------------------------------------
// Annex N.2 reference algorithm for the probabilistic distribution functions.
//
// The LRM defines the exact numeric behavior of $dist_uniform, $dist_normal,
// $dist_exponential, $dist_poisson, $dist_chi_square, $dist_t, and $dist_erlang
// by giving C source code for them. The functions below are a faithful
// transcription of that source. All randomness comes from a 32-bit
// linear-congruential state threaded through every draw, so a given seed always
// reproduces the same value (§20.14.2 repeatability) and every higher-level
// distribution is built on the same base generator.

// §N.2 uniform(): the base generator. It advances the seed with the 69069
// multiplier, forms a float in [1.0, 2.0) from the top bits of the new state
// (this relies on the IEEE 754 binary32 layout, as the reference notes), and
// rescales it onto [start, end).
static double RefUniform(int32_t* seed, int32_t start, int32_t end) {
  const double d = 0.00000011920928955078125;  // 2^-23
  double a = 0.0, b = 0.0;
  if (*seed == 0) *seed = 259341593;
  if (start >= end) {
    a = 0.0;
    b = 2147483647.0;
  } else {
    a = static_cast<double>(start);
    b = static_cast<double>(end);
  }
  // The multiply is taken mod 2^32 (unsigned) to match the reference's long
  // arithmetic without relying on signed overflow.
  *seed = static_cast<int32_t>(69069u * static_cast<uint32_t>(*seed) + 1u);
  uint32_t bits = (static_cast<uint32_t>(*seed) >> 9) | 0x3f800000u;
  float fs = 0.0F;
  std::memcpy(&fs, &bits, sizeof(fs));
  double c = static_cast<double>(fs);
  c = c + (c * d);
  c = ((b - a) * (c - 1.0)) + a;
  return c;
}

// §N.2 normal(): the Marsaglia polar method, drawing pairs from uniform(-1,1)
// until they fall inside the unit circle.
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

// §N.2 exponential(): inverse transform of a uniform(0,1) draw.
static double RefExponential(int32_t* seed, int32_t mean) {
  double n = RefUniform(seed, 0, 1);
  if (n != 0) n = -std::log(n) * mean;
  return n;
}

// §N.2 poisson(): counts uniform(0,1) products until they drop below e^-mean.
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

// §N.2 chi_square(): an odd degree contributes one squared normal; every pair
// of degrees adds twice an exponential(1).
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

// §N.2 t(): a standard normal divided by the root of a chi-square over its
// degrees of freedom.
static double RefT(int32_t* seed, int32_t deg_of_free) {
  double chi2 = RefChiSquare(seed, deg_of_free);
  double div = chi2 / static_cast<double>(deg_of_free);
  double root = std::sqrt(div);
  return RefNormal(seed, 0, 1) / root;
}

// §N.2 erlangian(): the product of k uniform(0,1) draws shaped by the mean.
static double RefErlangian(int32_t* seed, int32_t k, int32_t mean) {
  double x = 1.0;
  for (int32_t i = 1; i <= k; i++) x = x * RefUniform(seed, 0, 1);
  double a = static_cast<double>(mean);
  double b = static_cast<double>(k);
  return -a * std::log(x) / b;
}

// §N.2: every rtl_dist_* wrapper except uniform rounds its real draw to the
// nearest integer, preserving the sign by rounding the magnitude.
static int32_t RoundDistResult(double r) {
  if (r >= 0) return static_cast<int32_t>(r + 0.5);
  r = -r;
  return -static_cast<int32_t>(r + 0.5);
}

// §N.2 rtl_dist_uniform(): rounds toward the interval and clamps the result so
// it stays inside [start, end], handling the LONG_MAX and LONG_MIN edges the
// way the reference does (its long is the 32-bit integer modeled here).
static int32_t RtlDistUniform(int32_t* seed, int32_t start, int32_t end) {
  if (start >= end) return start;
  int32_t i = 0;
  if (end != INT32_MAX) {
    end++;
    double r = RefUniform(seed, start, end);
    i = r >= 0 ? static_cast<int32_t>(r) : static_cast<int32_t>(r - 1);
    if (i < start) i = start;
    if (i >= end) i = end - 1;
  } else if (start != INT32_MIN) {
    start--;
    double r = RefUniform(seed, start, end) + 1.0;
    i = r >= 0 ? static_cast<int32_t>(r) : static_cast<int32_t>(r - 1);
    if (i <= start) i = start + 1;
    if (i > end) i = end;
  } else {
    double r = (RefUniform(seed, start, end) + 2147483648.0) / 4294967295.0;
    r = r * 4294967296.0 - 2147483648.0;
    i = r >= 0 ? static_cast<int32_t>(r) : static_cast<int32_t>(r - 1);
  }
  return i;
}

// §N.2 rtl_dist_*: each guards the argument the reference requires to be
// positive and returns 0 otherwise (the diagnostic for that case is raised by
// ValidateDistArgs, §20.14.2). $dist_normal accepts any mean.
static int32_t RtlDistNormal(int32_t* seed, int32_t mean, int32_t sd) {
  return RoundDistResult(RefNormal(seed, mean, sd));
}
static int32_t RtlDistExponential(int32_t* seed, int32_t mean) {
  if (mean <= 0) return 0;
  return RoundDistResult(RefExponential(seed, mean));
}
static int32_t RtlDistPoisson(int32_t* seed, int32_t mean) {
  if (mean <= 0) return 0;
  return RefPoisson(seed, mean);
}
static int32_t RtlDistChiSquare(int32_t* seed, int32_t df) {
  if (df <= 0) return 0;
  return RoundDistResult(RefChiSquare(seed, df));
}
static int32_t RtlDistT(int32_t* seed, int32_t df) {
  if (df <= 0) return 0;
  return RoundDistResult(RefT(seed, df));
}
static int32_t RtlDistErlang(int32_t* seed, int32_t k, int32_t mean) {
  if (k <= 0) return 0;
  return RoundDistResult(RefErlangian(seed, k, mean));
}

// §20.14.2: the seed is an inout argument — a value goes in and a different
// value comes back. When the seed names a variable, the advanced LCG state
// produced by the §N.2 algorithm is written back, so consecutive calls walk the
// stream while a run that re-initializes the seed to its original value replays
// identically.
static void WriteBackSeed(const Expr* seed_arg, int32_t seed, SimContext& ctx,
                          Arena& arena) {
  if (seed_arg->kind != ExprKind::kIdentifier) return;
  Variable* var = ctx.FindVariable(seed_arg->text);
  if (var == nullptr) return;
  var->value =
      MakeLogic4VecVal(arena, var->value.width, static_cast<uint32_t>(seed));
}

// §20.14.2: mean, degree_of_freedom, and k_stage shall be greater than 0 for
// the distributions that consume them. A non-positive value leaves the
// distribution undefined, so it is reported; the draw still proceeds.
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
  // §20.14.2: report any argument the distribution requires to be positive.
  ValidateDistArgs(expr, ctx, arena, name);

  // §N.2: the seed is the 32-bit LCG state. Read it from the inout first
  // argument, run the reference algorithm (which advances it), then write the
  // advanced state back so the seed behaves as an inout argument (§20.14.2).
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

  WriteBackSeed(expr->args[0], seed, ctx, arena);
  return MakeLogic4VecVal(arena, 32,
                          static_cast<uint64_t>(static_cast<uint32_t>(result)));
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
