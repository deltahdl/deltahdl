#include "simulator/eval_string.h"

#include <algorithm>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

static uint8_t ByteAtChar(const Logic4Vec& packed, uint32_t i) {
  uint32_t nbytes = packed.width / 8;
  if (i >= nbytes) return 0;
  uint32_t byte_idx = nbytes - 1 - i;
  uint32_t word = (byte_idx * 8) / 64;
  uint32_t bit = (byte_idx * 8) % 64;
  if (word >= packed.nwords) return 0;
  return static_cast<uint8_t>((packed.words[word].aval >> bit) & 0xFF);
}

static Logic4Vec PackBytes(const std::vector<uint8_t>& bytes, Arena& arena) {
  uint32_t width = static_cast<uint32_t>(bytes.size()) * 8;
  if (width == 0) width = 8;
  auto out = MakeLogic4Vec(arena, width);
  for (size_t i = 0; i < bytes.size(); ++i) {
    auto byte_idx = static_cast<uint32_t>(bytes.size() - 1 - i);
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    out.words[word].aval |= static_cast<uint64_t>(bytes[i]) << bit;
  }
  return out;
}

Logic4Vec StripStringZeros(const Logic4Vec& packed, Arena& arena) {
  uint32_t nbytes = packed.width / 8;
  std::vector<uint8_t> kept;
  kept.reserve(nbytes);
  for (uint32_t i = 0; i < nbytes; ++i) {
    uint8_t b = ByteAtChar(packed, i);
    if (b != 0) kept.push_back(b);
  }
  return PackBytes(kept, arena);
}

void StringWriteByte(Variable* var, uint32_t idx, uint8_t byte_val,
                     Arena& arena) {
  if (!var) return;
  if (byte_val == 0) return;
  uint32_t nbytes = var->value.width / 8;
  if (idx >= nbytes) return;
  std::vector<uint8_t> bytes;
  bytes.reserve(nbytes);
  for (uint32_t i = 0; i < nbytes; ++i)
    bytes.push_back(ByteAtChar(var->value, i));
  bytes[idx] = byte_val;
  var->value = PackBytes(bytes, arena);
}

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

Logic4Vec StringToLogic4Vec(Arena& arena, std::string_view str) {
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

static void AssignStringToVar(Variable* var, Arena& arena,
                              std::string_view str) {
  var->value = StringToLogic4Vec(arena, str);
}

static Logic4Vec StringLen(const std::string& str, Arena& arena) {
  return MakeLogic4VecVal(arena, 32, str.size());
}

static void StringPutc(Variable* var, const std::string& str,
                       const Expr* call_expr, SimContext& ctx, Arena& arena) {
  if (call_expr->args.size() < 2) return;
  auto idx = EvalExpr(call_expr->args[0], ctx, arena).ToUint64();
  auto ch = EvalExpr(call_expr->args[1], ctx, arena).ToUint64();
  if ((ch & 0xFF) == 0) return;
  std::string copy = str;
  if (idx < copy.size()) {
    copy[idx] = static_cast<char>(ch & 0xFF);
    AssignStringToVar(var, arena, copy);
  }
}

static Logic4Vec StringGetc(const std::string& str, const Expr* call_expr,
                            SimContext& ctx, Arena& arena) {
  if (call_expr->args.empty()) return MakeLogic4VecVal(arena, 8, 0);
  auto idx = EvalExpr(call_expr->args[0], ctx, arena).ToUint64();
  if (idx >= str.size()) return MakeLogic4VecVal(arena, 8, 0);
  return MakeLogic4VecVal(arena, 8, static_cast<unsigned char>(str[idx]));
}

static Logic4Vec StringToupper(const std::string& str, Arena& arena) {
  std::string upper = str;
  for (auto& c : upper) c = static_cast<char>(std::toupper(c));
  return StringToLogic4Vec(arena, upper);
}

static Logic4Vec StringTolower(const std::string& str, Arena& arena) {
  std::string lower = str;
  for (auto& c : lower) c = static_cast<char>(std::tolower(c));
  return StringToLogic4Vec(arena, lower);
}

static std::string EvalArgAsString(const Expr* arg, SimContext& ctx,
                                   Arena& arena) {
  auto val = EvalExpr(arg, ctx, arena);
  return Logic4VecToString(val);
}

static Logic4Vec StringCompare(const std::string& str, const Expr* call_expr,
                               SimContext& ctx, Arena& arena) {
  if (call_expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  auto other = EvalArgAsString(call_expr->args[0], ctx, arena);
  int cmp = str.compare(other);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(cmp));
}

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

static int DigitValueForBase(char c, int base) {
  if ((base == 10 || base == 16) && c >= '0' && c <= '9') return c - '0';
  if (base == 16 && c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (base == 16 && c >= 'A' && c <= 'F') return c - 'A' + 10;
  if (base == 8 && c >= '0' && c <= '7') return c - '0';
  if (base == 2 && (c == '0' || c == '1')) return c - '0';
  return -1;
}

static Logic4Vec StringAtoBase(const std::string& str, int base, Arena& arena) {
  uint64_t val = 0;
  bool found_digit = false;
  for (char c : str) {
    if (c == '_') continue;
    int digit = DigitValueForBase(c, base);
    if (digit < 0) break;
    val = val * static_cast<uint64_t>(base) + static_cast<uint64_t>(digit);
    found_digit = true;
  }
  if (!found_digit) val = 0;
  return MakeLogic4VecVal(arena, 32, val);
}

static Logic4Vec StringAtoreal(const std::string& str, Arena& arena) {
  const char* start = str.c_str();
  char* end = nullptr;
  double d = std::strtod(start, &end);
  // The conversion only recognizes real constants, and the result is zero when
  // no digits were scanned. strtod additionally accepts digit-free spellings
  // such as "inf"/"nan"; these are not real constants, so force the result to
  // zero unless the scanned prefix actually contained a decimal digit.
  bool found_digit = false;
  for (const char* p = start; p < end; ++p) {
    if (*p >= '0' && *p <= '9') {
      found_digit = true;
      break;
    }
  }
  if (!found_digit) d = 0.0;
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  return MakeLogic4VecVal(arena, 64, bits);
}

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

bool TryEvalStringMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;

  if (!ctx.IsStringVariable(parts.var_name)) return false;

  auto* var = ctx.FindVariable(parts.var_name);
  std::string str = var ? Logic4VecToString(var->value) : "";

  StringMethodArgs args{var, str, expr, ctx, arena};
  if (DispatchReturningMethod(parts.method_name, args, out)) return true;
  return DispatchMutatingMethod(parts.method_name, args, out);
}

bool TryEvalStringProperty(std::string_view var_name, std::string_view prop,
                           SimContext& ctx, Arena& arena, Logic4Vec& out) {
  if (!ctx.IsStringVariable(var_name)) return false;
  if (prop != "len") return false;
  auto* var = ctx.FindVariable(var_name);
  std::string str = var ? Logic4VecToString(var->value) : "";
  out = StringLen(str, arena);
  return true;
}

}  // namespace delta
