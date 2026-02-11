#include "simulation/eval_string.h"

#include <algorithm>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

namespace delta {

// --- String <-> Logic4Vec helpers ---

static std::string Logic4VecToString(const Logic4Vec& vec) {
  uint32_t nbytes = vec.width / 8;
  std::string result;
  result.reserve(nbytes);
  for (uint32_t i = nbytes; i > 0; --i) {
    uint32_t byte_idx = i - 1;
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    if (word >= vec.nwords) continue;
    auto ch = static_cast<char>((vec.words[word].aval >> bit) & 0xFF);
    if (ch != 0) result += ch;
  }
  return result;
}

static Logic4Vec StringToLogic4Vec(Arena& arena, std::string_view str) {
  uint32_t width = static_cast<uint32_t>(str.size()) * 8;
  if (width == 0) width = 8;
  auto vec = MakeLogic4Vec(arena, width);
  for (size_t i = 0; i < str.size(); ++i) {
    auto byte_idx = static_cast<uint32_t>(str.size() - 1 - i);
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    vec.words[word].aval |=
        static_cast<uint64_t>(static_cast<unsigned char>(str[i])) << bit;
  }
  return vec;
}

// Assign a string value to an existing variable, resizing as needed.
static void AssignStringToVar(Variable* var, Arena& arena,
                              std::string_view str) {
  var->value = StringToLogic4Vec(arena, str);
}

// --- Individual method implementations ---

// §6.16.1: len() — returns string length.
static Logic4Vec StringLen(const std::string& str, Arena& arena) {
  return MakeLogic4VecVal(arena, 32, str.size());
}

// §6.16.2: putc(i, c) — replace byte at index i with character c.
static void StringPutc(Variable* var, const std::string& str,
                       const Expr* call_expr, SimContext& ctx, Arena& arena) {
  if (call_expr->args.size() < 2) return;
  auto idx = EvalExpr(call_expr->args[0], ctx, arena).ToUint64();
  auto ch = EvalExpr(call_expr->args[1], ctx, arena).ToUint64();
  std::string copy = str;
  if (idx < copy.size()) {
    copy[idx] = static_cast<char>(ch & 0xFF);
    AssignStringToVar(var, arena, copy);
  }
}

// §6.16.3: getc(i) — return byte at index i.
static Logic4Vec StringGetc(const std::string& str, const Expr* call_expr,
                            SimContext& ctx, Arena& arena) {
  if (call_expr->args.empty()) return MakeLogic4VecVal(arena, 8, 0);
  auto idx = EvalExpr(call_expr->args[0], ctx, arena).ToUint64();
  if (idx >= str.size()) return MakeLogic4VecVal(arena, 8, 0);
  return MakeLogic4VecVal(arena, 8, static_cast<unsigned char>(str[idx]));
}

// §6.16.4: toupper() — return uppercased copy.
static Logic4Vec StringToupper(const std::string& str, Arena& arena) {
  std::string upper = str;
  for (auto& c : upper) c = static_cast<char>(std::toupper(c));
  return StringToLogic4Vec(arena, upper);
}

// §6.16.5: tolower() — return lowercased copy.
static Logic4Vec StringTolower(const std::string& str, Arena& arena) {
  std::string lower = str;
  for (auto& c : lower) c = static_cast<char>(std::tolower(c));
  return StringToLogic4Vec(arena, lower);
}

// Extract the string value of an argument (identifier or string literal).
static std::string EvalArgAsString(const Expr* arg, SimContext& ctx,
                                   Arena& arena) {
  auto val = EvalExpr(arg, ctx, arena);
  return Logic4VecToString(val);
}

// §6.16.6: compare(s) — lexicographic compare.
static Logic4Vec StringCompare(const std::string& str, const Expr* call_expr,
                               SimContext& ctx, Arena& arena) {
  if (call_expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  auto other = EvalArgAsString(call_expr->args[0], ctx, arena);
  int cmp = str.compare(other);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(cmp));
}

// §6.16.7: icompare(s) — case-insensitive compare.
static Logic4Vec StringIcompare(const std::string& str, const Expr* call_expr,
                                SimContext& ctx, Arena& arena) {
  if (call_expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  auto other = EvalArgAsString(call_expr->args[0], ctx, arena);
  std::string a = str;
  std::string b = other;
  for (auto& c : a) c = static_cast<char>(std::tolower(c));
  for (auto& c : b) c = static_cast<char>(std::tolower(c));
  int cmp = a.compare(b);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(cmp));
}

// §6.16.8: substr(i, j) — extract substring from index i to j (inclusive).
static Logic4Vec StringSubstr(const std::string& str, const Expr* call_expr,
                              SimContext& ctx, Arena& arena) {
  if (call_expr->args.size() < 2) return StringToLogic4Vec(arena, "");
  auto i = EvalExpr(call_expr->args[0], ctx, arena).ToUint64();
  auto j = EvalExpr(call_expr->args[1], ctx, arena).ToUint64();
  if (i >= str.size() || j >= str.size() || i > j) {
    return StringToLogic4Vec(arena, "");
  }
  return StringToLogic4Vec(arena, str.substr(i, j - i + 1));
}

// §6.16.9: atoi() / atohex() / atooct() / atobin()
static Logic4Vec StringAtoBase(const std::string& str, int base, Arena& arena) {
  auto val = static_cast<uint64_t>(std::strtol(str.c_str(), nullptr, base));
  return MakeLogic4VecVal(arena, 32, val);
}

// §6.16.10: atoreal() — convert string to real.
static Logic4Vec StringAtoreal(const std::string& str, Arena& arena) {
  double d = std::strtod(str.c_str(), nullptr);
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  return MakeLogic4VecVal(arena, 64, bits);
}

// §6.16.11-14: itoa(i), hextoa(i), octtoa(i), bintoa(i)
static void StringXtoa(Variable* var, const Expr* call_expr, SimContext& ctx,
                       Arena& arena, int base) {
  if (call_expr->args.empty()) return;
  auto val = EvalExpr(call_expr->args[0], ctx, arena).ToUint64();
  std::string result;
  if (base == 10) {
    result = std::to_string(val);
  } else if (base == 16) {
    char buf[32];
    std::snprintf(buf, sizeof(buf), "%llx",
                  static_cast<unsigned long long>(val));
    result = buf;
  } else if (base == 8) {
    char buf[32];
    std::snprintf(buf, sizeof(buf), "%llo",
                  static_cast<unsigned long long>(val));
    result = buf;
  } else if (base == 2) {
    if (val == 0) {
      result = "0";
    } else {
      while (val > 0) {
        result += static_cast<char>('0' + (val & 1));
        val >>= 1;
      }
      std::reverse(result.begin(), result.end());
    }
  }
  AssignStringToVar(var, arena, result);
}

// §6.16.15: realtoa(r) — assign real string representation to variable.
static void StringRealtoa(Variable* var, const Expr* call_expr, SimContext& ctx,
                          Arena& arena) {
  if (call_expr->args.empty()) return;
  uint64_t bits = EvalExpr(call_expr->args[0], ctx, arena).ToUint64();
  double d = 0.0;
  std::memcpy(&d, &bits, sizeof(double));
  char buf[64];
  std::snprintf(buf, sizeof(buf), "%g", d);
  AssignStringToVar(var, arena, buf);
}

// --- Dispatch ---

// Bundle context to stay within the 5-argument limit.
struct StringMethodArgs {
  Variable* var;
  std::string str;
  const Expr* call_expr;
  SimContext& ctx;
  Arena& arena;
};

static bool DispatchReturningMethod(std::string_view method,
                                    const StringMethodArgs& a, Logic4Vec& out) {
  if (method == "len") {
    out = StringLen(a.str, a.arena);
    return true;
  }
  if (method == "getc") {
    out = StringGetc(a.str, a.call_expr, a.ctx, a.arena);
    return true;
  }
  if (method == "toupper") {
    out = StringToupper(a.str, a.arena);
    return true;
  }
  if (method == "tolower") {
    out = StringTolower(a.str, a.arena);
    return true;
  }
  if (method == "compare") {
    out = StringCompare(a.str, a.call_expr, a.ctx, a.arena);
    return true;
  }
  if (method == "icompare") {
    out = StringIcompare(a.str, a.call_expr, a.ctx, a.arena);
    return true;
  }
  if (method == "substr") {
    out = StringSubstr(a.str, a.call_expr, a.ctx, a.arena);
    return true;
  }
  if (method == "atoi") {
    out = StringAtoBase(a.str, 10, a.arena);
    return true;
  }
  if (method == "atohex") {
    out = StringAtoBase(a.str, 16, a.arena);
    return true;
  }
  if (method == "atooct") {
    out = StringAtoBase(a.str, 8, a.arena);
    return true;
  }
  if (method == "atobin") {
    out = StringAtoBase(a.str, 2, a.arena);
    return true;
  }
  if (method == "atoreal") {
    out = StringAtoreal(a.str, a.arena);
    return true;
  }
  return false;
}

static bool DispatchMutatingMethod(std::string_view method,
                                   const StringMethodArgs& a, Logic4Vec& out) {
  if (method == "putc") {
    StringPutc(a.var, a.str, a.call_expr, a.ctx, a.arena);
    out = MakeLogic4VecVal(a.arena, 1, 0);
    return true;
  }
  if (method == "itoa") {
    StringXtoa(a.var, a.call_expr, a.ctx, a.arena, 10);
    out = MakeLogic4VecVal(a.arena, 1, 0);
    return true;
  }
  if (method == "hextoa") {
    StringXtoa(a.var, a.call_expr, a.ctx, a.arena, 16);
    out = MakeLogic4VecVal(a.arena, 1, 0);
    return true;
  }
  if (method == "octtoa") {
    StringXtoa(a.var, a.call_expr, a.ctx, a.arena, 8);
    out = MakeLogic4VecVal(a.arena, 1, 0);
    return true;
  }
  if (method == "bintoa") {
    StringXtoa(a.var, a.call_expr, a.ctx, a.arena, 2);
    out = MakeLogic4VecVal(a.arena, 1, 0);
    return true;
  }
  if (method == "realtoa") {
    StringRealtoa(a.var, a.call_expr, a.ctx, a.arena);
    out = MakeLogic4VecVal(a.arena, 1, 0);
    return true;
  }
  return false;
}

// §6.16: Try to evaluate a string method call.
// Returns true and sets `out` if the call is a string method.
bool TryEvalStringMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out) {
  // String method calls appear as kCall where lhs is a kMemberAccess.
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;

  auto* access = expr->lhs;
  if (!access->lhs || access->lhs->kind != ExprKind::kIdentifier) return false;
  if (!access->rhs || access->rhs->kind != ExprKind::kIdentifier) return false;

  auto var_name = access->lhs->text;
  auto method_name = access->rhs->text;

  if (!ctx.IsStringVariable(var_name)) return false;

  auto* var = ctx.FindVariable(var_name);
  std::string str = var ? Logic4VecToString(var->value) : "";

  StringMethodArgs args{var, str, expr, ctx, arena};
  if (DispatchReturningMethod(method_name, args, out)) return true;
  return DispatchMutatingMethod(method_name, args, out);
}

}  // namespace delta
