#include <bit>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

static uint32_t CountOnesInVec(const Logic4Vec& val) {
  uint32_t count = 0;
  for (uint32_t i = 0; i < val.nwords; ++i) {
    uint64_t known_ones = val.words[i].aval & ~val.words[i].bval;
    count += static_cast<uint32_t>(std::popcount(known_ones));
  }
  return count;
}

static Logic4Vec EvalClog2(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  uint64_t v = EvalExpr(expr->args[0], ctx, arena).ToUint64();
  if (v <= 1) return MakeLogic4VecVal(arena, 32, 0);
  int result = 0;
  uint64_t shifted = v - 1;
  while (shifted > 0) {
    shifted >>= 1;
    ++result;
  }
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(result));
}

static Logic4Vec EvalSignCast(const Expr* expr, SimContext& ctx, Arena& arena,
                              bool make_signed) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  val.is_signed = make_signed;
  return val;
}

static Logic4Vec EvalCountones(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  auto val = PackBitStreamOperand(expr->args[0], ctx, arena);
  return MakeLogic4VecVal(arena, 32, CountOnesInVec(val));
}

static Logic4Vec EvalOnehot(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  auto val = PackBitStreamOperand(expr->args[0], ctx, arena);
  uint64_t result = (CountOnesInVec(val) == 1) ? 1 : 0;
  return MakeLogic4VecVal(arena, 1, result);
}

static Logic4Vec EvalOnehot0(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 1);
  auto val = PackBitStreamOperand(expr->args[0], ctx, arena);
  uint64_t result = (CountOnesInVec(val) <= 1) ? 1 : 0;
  return MakeLogic4VecVal(arena, 1, result);
}

static Logic4Vec EvalIsunknown(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  auto val = PackBitStreamOperand(expr->args[0], ctx, arena);
  return MakeLogic4VecVal(arena, 1, HasUnknownBits(val) ? 1 : 0);
}

std::string ExtractStrArg(const Expr* arg) {
  auto text = arg->text;
  if (text.size() >= 2 && text.front() == '"') {
    return std::string(text.substr(1, text.size() - 2));
  }
  return std::string(text);
}

static std::string ResolvePlusargPattern(const Expr* arg, SimContext& ctx,
                                         Arena& arena) {
  if (arg->kind == ExprKind::kStringLiteral) {
    return ExtractStrArg(arg);
  }
  return FormatValueAsString(EvalExpr(arg, ctx, arena));
}

static Logic4Vec EvalTestPlusargs(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  std::string prefix = ResolvePlusargPattern(expr->args[0], ctx, arena);
  for (const auto& arg : ctx.GetPlusArgs()) {
    if (arg.substr(0, prefix.size()) == prefix) {
      return MakeLogic4VecVal(arena, 32, 1);
    }
  }
  return MakeLogic4VecVal(arena, 32, 0);
}

static char SplitUserString(const std::string& user, std::string& prefix_out) {
  auto pct = user.find('%');
  if (pct == std::string::npos) {
    prefix_out = user;
    return '\0';
  }
  prefix_out = user.substr(0, pct);
  size_t i = pct + 1;
  while (i < user.size() && user[i] >= '0' && user[i] <= '9') ++i;
  if (i >= user.size()) return '\0';
  char c = user[i];
  if (c >= 'A' && c <= 'Z') c = static_cast<char>(c - 'A' + 'a');
  return c;
}

static int PlusargIntegerBase(char conv) {
  switch (conv) {
    case 'd':
      return 10;
    case 'o':
      return 8;
    case 'h':
    case 'x':
      return 16;
    case 'b':
      return 2;
    default:
      return 0;
  }
}

static bool DecodePlusargDigit(char c, int& digit) {
  if (c >= '0' && c <= '9') {
    digit = c - '0';
    return true;
  }
  if (c >= 'a' && c <= 'f') {
    digit = c - 'a' + 10;
    return true;
  }
  if (c >= 'A' && c <= 'F') {
    digit = c - 'A' + 10;
    return true;
  }
  return false;
}

struct PlusargDigit {
  int val = 0;
  bool is_x = false;
  bool is_z = false;
};

static bool IsPlusargXZDigit(char c) {
  return c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?';
}

static bool CollectPlusargDigits(const std::string& s, int base,
                                 std::vector<PlusargDigit>& digits) {
  for (char c : s) {
    if (c == '_' && !digits.empty()) continue;
    if (IsPlusargXZDigit(c)) {
      bool is_x = (c == 'x' || c == 'X');
      digits.push_back({0, is_x, !is_x});
      continue;
    }
    int digit = 0;
    if (!DecodePlusargDigit(c, digit) || digit >= base) return false;
    digits.push_back({digit, false, false});
  }
  return !digits.empty();
}

static Logic4Vec PackPlusargDigits(Arena& arena,
                                   const std::vector<PlusargDigit>& digits,
                                   uint32_t bits_per_digit, uint32_t width) {
  auto vec = MakeLogic4VecVal(arena, width, 0);
  for (size_t i = 0; i < digits.size(); ++i) {
    const PlusargDigit& d = digits[digits.size() - 1 - i];
    for (uint32_t b = 0; b < bits_per_digit; ++b) {
      uint32_t bit = static_cast<uint32_t>(i) * bits_per_digit + b;
      if (bit >= width) break;
      bool a = d.is_x || (!d.is_z && (((d.val >> b) & 1) != 0));
      bool bb = d.is_x || d.is_z;
      if (a) vec.words[bit / 64].aval |= uint64_t{1} << (bit % 64);
      if (bb) vec.words[bit / 64].bval |= uint64_t{1} << (bit % 64);
    }
  }
  return vec;
}

static Logic4Vec MakePlusargAllXZ(Arena& arena, uint32_t width, bool is_x) {
  auto vec = MakeLogic4VecVal(arena, width, 0);
  for (uint32_t bit = 0; bit < width; ++bit) {
    if (is_x) vec.words[bit / 64].aval |= uint64_t{1} << (bit % 64);
    vec.words[bit / 64].bval |= uint64_t{1} << (bit % 64);
  }
  return vec;
}

struct PlusargDest {
  Variable* var;
  std::string name;
  uint32_t width;
  bool is_string = false;
};

static void StorePlusargDecimal(const PlusargDest& dest, const std::string& s,
                                Arena& arena) {
  size_t i = 0;
  bool neg = false;
  if (s[i] == '+' || s[i] == '-') {
    neg = (s[i] == '-');
    ++i;
  }
  if (i + 1 == s.size() && IsPlusargXZDigit(s[i])) {
    bool is_x = (s[i] == 'x' || s[i] == 'X');
    dest.var->value = MakePlusargAllXZ(arena, dest.width, is_x);
    return;
  }
  uint64_t mag = 0;
  bool any = false;
  for (; i < s.size(); ++i) {
    char c = s[i];
    if (c == '_' && any) continue;
    if (c < '0' || c > '9') {
      dest.var->value = MakeAllX(arena, dest.width);
      return;
    }
    mag = mag * 10 + static_cast<uint64_t>(c - '0');
    any = true;
  }
  if (!any) {
    dest.var->value = MakeAllX(arena, dest.width);
    return;
  }
  uint64_t stored =
      neg ? static_cast<uint64_t>(-static_cast<int64_t>(mag)) : mag;
  dest.var->value = MakeLogic4VecVal(arena, dest.width, stored);
}

static void StorePlusargReal(const PlusargDest& dest,
                             const std::string& remainder, SimContext& ctx,
                             Arena& arena) {
  if (remainder.empty()) {
    dest.var->value = MakeLogic4VecVal(arena, dest.width, 0);
    return;
  }
  const char* begin = remainder.c_str();
  char* end = nullptr;
  double d = std::strtod(begin, &end);
  if (end != begin + remainder.size()) {
    dest.var->value = MakeAllX(arena, dest.width);
    return;
  }
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  auto vec = MakeLogic4VecVal(arena, dest.width, bits);
  if (ctx.IsRealVariable(dest.name)) vec.is_real = true;
  dest.var->value = vec;
}

static void StorePlusargInteger(const PlusargDest& dest, char conv,
                                const std::string& remainder, Arena& arena) {
  if (remainder.empty()) {
    dest.var->value = MakeLogic4VecVal(arena, dest.width, 0);
    return;
  }
  int base = PlusargIntegerBase(conv);
  if (base == 0) {
    dest.var->value = MakeAllX(arena, dest.width);
    return;
  }
  if (base == 10) {
    StorePlusargDecimal(dest, remainder, arena);
    return;
  }
  std::vector<PlusargDigit> digits;
  if (!CollectPlusargDigits(remainder, base, digits)) {
    dest.var->value = MakeAllX(arena, dest.width);
    return;
  }
  uint32_t bits_per_digit = base == 2 ? 1 : (base == 8 ? 3 : 4);
  dest.var->value =
      PackPlusargDigits(arena, digits, bits_per_digit, dest.width);
}

static void StorePlusargConverted(const PlusargDest& dest, char conv,
                                  const std::string& remainder, SimContext& ctx,
                                  Arena& arena) {
  if (conv == 's') {
    uint32_t w = dest.is_string ? static_cast<uint32_t>(remainder.size()) * 8
                                : dest.width;
    dest.var->value = ScanStringToVec(arena, remainder, w);
    return;
  }

  if (conv == 'e' || conv == 'f' || conv == 'g') {
    StorePlusargReal(dest, remainder, ctx, arena);
    return;
  }

  StorePlusargInteger(dest, conv, remainder, arena);
}

static void StorePlusargValue(const PlusargDest& dest, char conv,
                              const std::string& remainder, SimContext& ctx,
                              Arena& arena) {
  if (!dest.var) return;
  StorePlusargConverted(dest, conv, remainder, ctx, arena);
  dest.var->NotifyWatchers();
}

static Logic4Vec EvalValuePlusargs(const Expr* expr, SimContext& ctx,
                                   Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 32, 0);
  std::string user = ResolvePlusargPattern(expr->args[0], ctx, arena);
  std::string prefix;
  char conv = SplitUserString(user, prefix);

  Variable* var = nullptr;
  std::string var_name;
  bool is_string = false;
  if (expr->args[1]->kind == ExprKind::kIdentifier) {
    var_name = std::string(expr->args[1]->text);
    var = ctx.FindVariable(var_name);
    is_string = var != nullptr && ctx.IsStringVariable(var_name);
  }
  uint32_t dest_width = (var && var->value.width) ? var->value.width : 32;
  PlusargDest dest{var, var_name, dest_width, is_string};

  for (const auto& arg : ctx.GetPlusArgs()) {
    if (arg.substr(0, prefix.size()) != prefix) continue;
    std::string remainder = arg.substr(prefix.size());
    StorePlusargValue(dest, conv, remainder, ctx, arena);
    return MakeLogic4VecVal(arena, 32, 1);
  }
  return MakeLogic4VecVal(arena, 32, 0);
}

static std::string TypenameForVariable(const Variable* var) {
  uint32_t w = var->value.width;

  if (!var->is_4state && var->is_signed && w == 32) return "int";
  std::string base = var->is_4state ? "logic" : "bit";
  if (w <= 1) return base;
  return base + "[" + std::to_string(w - 1) + ":0]";
}

Logic4Vec EvalTypenameOfExpression(const Expr* expr, SimContext& ctx,
                                   Arena& arena) {
  if (expr->args.empty()) {
    return StringToLogic4Vec(arena, "logic");
  }
  const auto* arg = expr->args[0];

  if (arg->kind == ExprKind::kIdentifier) {
    if (const auto* var = ctx.FindVariable(arg->text)) {
      return StringToLogic4Vec(arena, TypenameForVariable(var));
    }
  }
  return StringToLogic4Vec(arena, "logic");
}

std::string EvalStringArg(const Expr* arg, SimContext& ctx, Arena& arena) {
  auto val = EvalExpr(arg, ctx, arena);
  uint32_t nbytes = val.width / 8;
  std::string result;
  for (uint32_t i = nbytes; i > 0; --i) {
    uint32_t byte_idx = i - 1;
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    if (word >= val.nwords) continue;
    auto ch = static_cast<char>((val.words[word].aval >> bit) & 0xFF);
    if (ch != 0) result += ch;
  }
  return result;
}

static bool TryFormatArgFromByteArray(const Expr* arg, SimContext& ctx,
                                      std::string& out) {
  if (arg == nullptr || arg->kind != ExprKind::kIdentifier) return false;
  const ArrayInfo* ai = ctx.FindArrayInfo(arg->text);
  if (ai == nullptr || ai->is_dynamic || ai->is_queue ||
      ai->elem_type_kind != DataTypeKind::kByte) {
    return false;
  }
  std::string s;
  for (uint32_t i = 0; i < ai->size; ++i) {
    uint32_t idx =
        ai->is_descending ? (ai->lo + ai->size - 1 - i) : (ai->lo + i);
    std::string ename =
        std::string(arg->text) + "[" + std::to_string(idx) + "]";
    Variable* elem = ctx.FindVariable(ename);
    if (elem == nullptr) continue;
    char c = static_cast<char>(elem->value.ToUint64() & 0xFF);
    if (c != 0) s += c;
  }
  out = s;
  return true;
}

std::string ResolveFormatArg(const Expr* arg, SimContext& ctx, Arena& arena) {
  if (arg && arg->kind == ExprKind::kStringLiteral) {
    return ExtractFormatString(arg);
  }
  std::string from_array;
  if (TryFormatArgFromByteArray(arg, ctx, from_array)) return from_array;
  return EvalStringArg(arg, ctx, arena);
}

enum class SpecifierScan : std::uint8_t {
  kLiteralPercent,
  kTruncated,
  kComplete
};

static SpecifierScan ScanFormatSpecifier(const std::string& fmt, size_t& i,
                                         bool& consumes) {
  consumes = false;
  char c = fmt[i + 1];
  if (c == '%') {
    ++i;
    return SpecifierScan::kLiteralPercent;
  }
  size_t j = i + 1;
  while (j < fmt.size() && fmt[j] >= '0' && fmt[j] <= '9') ++j;
  if (j >= fmt.size()) return SpecifierScan::kTruncated;
  char spec = fmt[j];
  if (spec >= 'A' && spec <= 'Z') spec = static_cast<char>(spec - 'A' + 'a');
  consumes = (spec != 'm' && spec != 'l');
  i = j;
  return SpecifierScan::kComplete;
}

size_t CountConsumingSpecifiers(const std::string& fmt) {
  size_t n = 0;
  for (size_t i = 0; i + 1 < fmt.size(); ++i) {
    if (fmt[i] != '%') continue;
    bool consumes = false;
    SpecifierScan scan = ScanFormatSpecifier(fmt, i, consumes);
    if (scan == SpecifierScan::kLiteralPercent) continue;
    if (scan == SpecifierScan::kTruncated) break;
    if (consumes) ++n;
  }
  return n;
}

void WarnIfArgCountMismatch(SimContext& ctx, std::string_view task_name,
                            const std::string& fmt, size_t supplied,
                            SourceLoc loc) {
  size_t required = CountConsumingSpecifiers(fmt);
  if (supplied == required) return;
  std::string msg = std::string(task_name) + ": format-specifier count (" +
                    std::to_string(required) +
                    ") does not match supplied argument count (" +
                    std::to_string(supplied) + ")";
  ctx.GetDiag().Warning(loc, std::move(msg), Subclause("21.3.3"));
}

static Logic4Vec EvalSformatf(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return StringToLogic4Vec(arena, "");
  std::string fmt = ResolveFormatArg(expr->args[0], ctx, arena);
  WarnIfArgCountMismatch(ctx, "$sformatf", fmt, expr->args.size() - 1,
                         expr->range.start);
  std::string result = FormatDisplayArgs(expr, 0, fmt, ctx, arena);
  Logic4Vec out = StringToLogic4Vec(arena, result);
  out.is_string = true;
  return out;
}

static Logic4Vec EvalItor(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  double d = RealValueOf(val);
  if (val.is_real) d = std::round(d);
  return MakeRealVec(arena, d, 64);
}

static Logic4Vec EvalRtoi(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  auto truncated = static_cast<int64_t>(RealValueOf(val));
  Logic4Vec out = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(truncated));
  out.is_signed = true;
  return out;
}

static Logic4Vec EvalBitstoreal(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  Logic4Vec out = MakeLogic4VecVal(arena, 64, val.ToUint64());
  out.is_real = true;
  return out;
}

static Logic4Vec EvalRealtobits(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  double d = RealValueOf(EvalExpr(expr->args[0], ctx, arena));
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  return MakeLogic4VecVal(arena, 64, bits);
}

static uint32_t CountMatchingBits(const Logic4Vec& val, const bool match[4]) {
  uint32_t count = 0;
  for (uint32_t i = 0; i < val.nwords; ++i) {
    uint64_t a = val.words[i].aval;
    uint64_t b = val.words[i].bval;
    if (match[1]) count += static_cast<uint32_t>(std::popcount(a & ~b));
    if (match[0]) count += static_cast<uint32_t>(std::popcount(~a & ~b));
    if (match[3]) count += static_cast<uint32_t>(std::popcount(a & b));
    if (match[2]) count += static_cast<uint32_t>(std::popcount(~a & b));
  }
  if (match[0] && val.width < val.nwords * 64) {
    count -= val.nwords * 64 - val.width;
  }
  return count;
}

static Logic4Vec EvalCountbits(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 32, 0);
  auto val = PackBitStreamOperand(expr->args[0], ctx, arena);
  bool match[4] = {};
  for (size_t i = 1; i < expr->args.size(); ++i) {
    auto pat = EvalExpr(expr->args[i], ctx, arena);
    uint64_t a = pat.nwords > 0 ? pat.words[0].aval & 1 : 0;
    uint64_t b = pat.nwords > 0 ? pat.words[0].bval & 1 : 0;
    match[a + b * 2] = true;
  }
  return MakeLogic4VecVal(arena, 32, CountMatchingBits(val, match));
}

static Logic4Vec EvalConversionSysCall(const Expr* expr, SimContext& ctx,
                                       Arena& arena, std::string_view name) {
  if (name == "$itor") return EvalItor(expr, ctx, arena);
  if (name == "$rtoi") return EvalRtoi(expr, ctx, arena);
  if (name == "$bitstoreal") return EvalBitstoreal(expr, ctx, arena);
  if (name == "$realtobits") return EvalRealtobits(expr, ctx, arena);
  if (name == "$shortrealtobits") {
    if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
    auto val = EvalExpr(expr->args[0], ctx, arena);
    auto f = static_cast<float>(RealValueOf(val));
    uint32_t fbits = 0;
    std::memcpy(&fbits, &f, sizeof(float));
    return MakeLogic4VecVal(arena, 32, fbits);
  }
  if (name == "$bitstoshortreal") {
    uint64_t fbits =
        expr->args.empty() ? 0 : EvalExpr(expr->args[0], ctx, arena).ToUint64();
    auto result = MakeLogic4VecVal(arena, 32, fbits & 0xFFFFFFFFu);
    result.is_real = true;
    return result;
  }
  if (name == "$countbits") return EvalCountbits(expr, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

static bool FlattenParamRefName(const Expr* e, std::string& out) {
  if (e->kind == ExprKind::kIdentifier) {
    if (!e->scope_prefix.empty()) {
      out += e->scope_prefix;
      out += '.';
    }
    out += e->text;
    return true;
  }
  if (e->kind == ExprKind::kMemberAccess && e->lhs != nullptr &&
      e->rhs != nullptr) {
    if (!FlattenParamRefName(e->lhs, out)) return false;
    out += '.';
    return FlattenParamRefName(e->rhs, out);
  }
  return false;
}

static bool IsUnboundedClassParam(const std::string& name, SimContext& ctx) {
  const ClassObject* obj = ctx.CurrentThis();
  return obj != nullptr && obj->unbounded_params.count(name) != 0;
}

static Logic4Vec EvalIsunbounded(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  if (!expr->args.empty()) {
    std::string name;
    if (FlattenParamRefName(expr->args[0], name)) {
      bool ub = IsUnboundedClassParam(name, ctx) || ctx.IsUnboundedParam(name);
      return MakeLogic4VecVal(arena, 1, ub ? 1 : 0);
    }
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

Logic4Vec EvalUtilitySysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::string_view name) {
  if (name == "$clog2") return EvalClog2(expr, ctx, arena);
  if (name == "$bits") return EvalBits(expr, ctx, arena);
  if (name == "$signed") return EvalSignCast(expr, ctx, arena, true);
  if (name == "$unsigned") return EvalSignCast(expr, ctx, arena, false);
  if (name == "$countones") return EvalCountones(expr, ctx, arena);
  if (name == "$onehot") return EvalOnehot(expr, ctx, arena);
  if (name == "$onehot0") return EvalOnehot0(expr, ctx, arena);
  if (name == "$isunknown") return EvalIsunknown(expr, ctx, arena);
  if (name == "$isunbounded") return EvalIsunbounded(expr, ctx, arena);
  if (name == "$cast") return EvalCastSysFunc(expr, ctx, arena);
  if (name == "$test$plusargs") return EvalTestPlusargs(expr, ctx, arena);
  if (name == "$value$plusargs") return EvalValuePlusargs(expr, ctx, arena);
  if (name == "$typename") return EvalTypename(expr, ctx, arena);
  if (name == "$sformatf") return EvalSformatf(expr, ctx, arena);
  return EvalConversionSysCall(expr, ctx, arena, name);
}

}  // namespace delta
