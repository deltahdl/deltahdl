#include <bit>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
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

static Logic4Vec EvalBits(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);

  auto* arg = expr->args[0];
  if (arg->kind == ExprKind::kIdentifier) {
    uint32_t tw = ctx.FindTypeWidth(arg->text);
    if (tw > 0) return MakeLogic4VecVal(arena, 32, tw);
  }
  auto val = EvalExpr(arg, ctx, arena);
  return MakeLogic4VecVal(arena, 32, val.width);
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
  auto val = EvalExpr(expr->args[0], ctx, arena);
  return MakeLogic4VecVal(arena, 32, CountOnesInVec(val));
}

static Logic4Vec EvalOnehot(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  uint64_t result = (CountOnesInVec(val) == 1) ? 1 : 0;
  return MakeLogic4VecVal(arena, 1, result);
}

static Logic4Vec EvalOnehot0(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 1);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  uint64_t result = (CountOnesInVec(val) <= 1) ? 1 : 0;
  return MakeLogic4VecVal(arena, 1, result);
}

static Logic4Vec EvalIsunknown(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  return MakeLogic4VecVal(arena, 1, HasUnknownBits(val) ? 1 : 0);
}

std::string ExtractStrArg(const Expr* arg) {
  auto text = arg->text;
  if (text.size() >= 2 && text.front() == '"') {
    return std::string(text.substr(1, text.size() - 2));
  }
  return std::string(text);
}

// §21.6: a plusarg search string is supplied either as a string literal or as
// an integral variable whose packed bytes are read back as text. For the
// variable form, FormatValueAsString drops the all-zero (high) padding bytes,
// which discharges the rule that leading nulls are ignored when matching.
static std::string ResolvePlusargPattern(const Expr* arg, SimContext& ctx,
                                         Arena& arena) {
  if (arg->kind == ExprKind::kStringLiteral) {
    return ExtractStrArg(arg);
  }
  return FormatValueAsString(EvalExpr(arg, ctx, arena));
}

static Logic4Vec EvalTestPlusargs(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  // §21.6: the search string never carries the command-line '+' sign; plusargs
  // are stored without it, so a plain prefix comparison applies.
  std::string prefix = ResolvePlusargPattern(expr->args[0], ctx, arena);
  // §21.6: plusargs are examined in the order supplied; a plusarg whose prefix
  // matches every character of the search string yields a nonzero result.
  for (const auto& arg : ctx.GetPlusArgs()) {
    if (arg.substr(0, prefix.size()) == prefix) {
      return MakeLogic4VecVal(arena, 1, 1);
    }
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

// §21.6: the user_string of $value$plusargs has the form
// "plusarg_string format_string", where the trailing format string is a
// $display-style specifier. Splits off the matching prefix and returns the
// conversion letter folded to lowercase ('\0' when no specifier is present).
// Leading-zero and width digits after '%' are accepted but not otherwise acted
// on, matching the "leading 0 forms are valid" allowance.
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

// §21.6: validate and convert a plusarg remainder under an integer conversion
// (%d/%o/%h/%x/%b). Returns false if any character is illegal for the radix so
// the caller can store the 'bx fill the clause mandates.
static bool ParsePlusargInteger(const std::string& s, char conv, uint64_t& out,
                                bool& negative) {
  out = 0;
  negative = false;
  int base = 0;
  switch (conv) {
    case 'd':
      base = 10;
      break;
    case 'o':
      base = 8;
      break;
    case 'h':
    case 'x':
      base = 16;
      break;
    case 'b':
      base = 2;
      break;
    default:
      return false;
  }
  size_t i = 0;
  if (base == 10 && i < s.size() && (s[i] == '+' || s[i] == '-')) {
    negative = (s[i] == '-');
    ++i;
  }
  if (i >= s.size()) return false;
  for (; i < s.size(); ++i) {
    char c = s[i];
    int digit = 0;
    if (c >= '0' && c <= '9')
      digit = c - '0';
    else if (c >= 'a' && c <= 'f')
      digit = c - 'a' + 10;
    else if (c >= 'A' && c <= 'F')
      digit = c - 'A' + 10;
    else
      return false;
    if (digit >= base) return false;
    out = out * static_cast<uint64_t>(base) + static_cast<uint64_t>(digit);
  }
  return true;
}

// §21.6: place a converted string remainder into a fixed-width destination,
// right-justified so the trailing characters occupy the low-order bytes. A
// remainder longer than the destination is truncated; a shorter one leaves the
// high bytes zero, giving the zero-padded result the clause requires.
static Logic4Vec PackStringIntoWidth(Arena& arena, const std::string& s,
                                     uint32_t width) {
  auto vec = MakeLogic4Vec(arena, width);
  uint32_t nbytes = width / 8;
  for (size_t i = 0; i < s.size() && i < nbytes; ++i) {
    char ch = s[s.size() - 1 - i];
    uint32_t bit_off = static_cast<uint32_t>(i) * 8;
    uint32_t word = bit_off / 64;
    uint32_t bit = bit_off % 64;
    vec.words[word].aval |=
        static_cast<uint64_t>(static_cast<unsigned char>(ch)) << bit;
  }
  return vec;
}

// §21.6: convert the remainder of a matching plusarg into `var` according to
// the format string's conversion code. The stored value is automatically zero-
// padded or truncated to the variable width by MakeLogic4VecVal.
static void StorePlusargValue(Variable* var, const std::string& name, char conv,
                              const std::string& remainder, SimContext& ctx,
                              Arena& arena) {
  if (!var) return;
  uint32_t width = var->value.width ? var->value.width : 32;

  // §21.6: %s performs no numeric conversion; the characters are stored as is.
  if (conv == 's') {
    var->value = PackStringIntoWidth(arena, remainder, width);
    return;
  }

  // §21.6: %e/%f/%g convert to a real value, stored as its 64-bit IEEE pattern.
  if (conv == 'e' || conv == 'f' || conv == 'g') {
    if (remainder.empty()) {
      var->value = MakeLogic4VecVal(arena, width, 0);
      return;
    }
    const char* begin = remainder.c_str();
    char* end = nullptr;
    double d = std::strtod(begin, &end);
    if (end != begin + remainder.size()) {
      var->value = MakeAllX(arena, width);
      return;
    }
    uint64_t bits = 0;
    std::memcpy(&bits, &d, sizeof(double));
    auto vec = MakeLogic4VecVal(arena, width, bits);
    if (ctx.IsRealVariable(name)) vec.is_real = true;
    var->value = vec;
    return;
  }

  // §21.6: an empty remainder stores the value zero for integer conversions.
  if (remainder.empty()) {
    var->value = MakeLogic4VecVal(arena, width, 0);
    return;
  }

  uint64_t mag = 0;
  bool negative = false;
  if (!ParsePlusargInteger(remainder, conv, mag, negative)) {
    // §21.6: a remainder containing characters illegal for the conversion is
    // reported by writing the destination with 'bx.
    var->value = MakeAllX(arena, width);
    return;
  }
  // §21.6: a negative value is treated as larger than the variable, so its
  // two's-complement low-order bits fall through MakeLogic4VecVal's truncation.
  uint64_t stored =
      negative ? static_cast<uint64_t>(-static_cast<int64_t>(mag)) : mag;
  var->value = MakeLogic4VecVal(arena, width, stored);
}

static Logic4Vec EvalValuePlusargs(const Expr* expr, SimContext& ctx,
                                   Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 1, 0);
  std::string user = ResolvePlusargPattern(expr->args[0], ctx, arena);
  std::string prefix;
  char conv = SplitUserString(user, prefix);

  Variable* var = nullptr;
  std::string var_name;
  if (expr->args[1]->kind == ExprKind::kIdentifier) {
    var_name = std::string(expr->args[1]->text);
    var = ctx.FindVariable(var_name);
  }

  // §21.6: the first plusarg (in command-line order) whose prefix matches the
  // plusarg_string supplies the remainder available for conversion.
  for (const auto& arg : ctx.GetPlusArgs()) {
    if (arg.substr(0, prefix.size()) != prefix) continue;
    std::string remainder = arg.substr(prefix.size());
    StorePlusargValue(var, var_name, conv, remainder, ctx, arena);
    return MakeLogic4VecVal(arena, 1, 1);
  }
  // §21.6: with no match the function returns zero, leaves the variable
  // unmodified, and issues no warning.
  return MakeLogic4VecVal(arena, 1, 0);
}

static std::string TypenameForVariable(const Variable* var) {
  uint32_t w = var->value.width;

  if (!var->is_4state && var->is_signed && w == 32) return "int";
  std::string base = var->is_4state ? "logic" : "bit";
  if (w <= 1) return base;
  return base + "[" + std::to_string(w - 1) + ":0]";
}

static Logic4Vec EvalTypename(const Expr* expr, SimContext& ctx, Arena& arena) {
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

// §21.3.4.3 / §21.3.1 / §21.4: read a system-task argument as text. A string
// literal yields its quoted contents; any other expression has its packed-byte
// value decoded back into a std::string, dropping all-zero (high) padding
// bytes. Shared with eval_systask_io.cpp / eval_systask_readmem.cpp.
std::string EvalStringArg(const Expr* arg, SimContext& ctx, Arena& arena) {
  if (arg->kind == ExprKind::kStringLiteral) return ExtractStrArg(arg);
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

// §21.3.3 N10: a format argument may be supplied as a string literal or as
// any expression whose packed-byte value encodes the formatting string.
// Shared with eval_systask_io.cpp.
std::string ResolveFormatArg(const Expr* arg, SimContext& ctx, Arena& arena) {
  if (arg && arg->kind == ExprKind::kStringLiteral) {
    return ExtractFormatString(arg);
  }
  return EvalStringArg(arg, ctx, arena);
}

// §21.3.3: counts %-introduced specifiers that consume an argument value,
// excluding %% literals and %m/%l self-supplied specifiers.
size_t CountConsumingSpecifiers(const std::string& fmt) {
  size_t n = 0;
  for (size_t i = 0; i + 1 < fmt.size(); ++i) {
    if (fmt[i] != '%') continue;
    char c = fmt[i + 1];
    if (c == '%') {
      ++i;
      continue;
    }
    size_t j = i + 1;
    while (j < fmt.size() && fmt[j] >= '0' && fmt[j] <= '9') ++j;
    if (j >= fmt.size()) break;
    char spec = fmt[j];
    if (spec >= 'A' && spec <= 'Z') spec = static_cast<char>(spec - 'A' + 'a');
    if (spec != 'm' && spec != 'l') ++n;
    i = j;
  }
  return n;
}

// §21.3.3 N14: when the supplied argument count does not match the number of
// consuming format specifiers, the application shall issue a warning and
// continue execution.
void WarnIfArgCountMismatch(SimContext& ctx, std::string_view task_name,
                            const std::string& fmt, size_t supplied) {
  size_t required = CountConsumingSpecifiers(fmt);
  if (supplied == required) return;
  std::string msg = std::string(task_name) + ": format-specifier count (" +
                    std::to_string(required) +
                    ") does not match supplied argument count (" +
                    std::to_string(supplied) + ")";
  ctx.GetDiag().Warning({}, std::move(msg));
}

static Logic4Vec EvalSformatf(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return StringToLogic4Vec(arena, "");
  // §21.3.3 N10: accept a string literal or any integral / byte-array /
  // string-typed expression as the format argument.
  std::string fmt = ResolveFormatArg(expr->args[0], ctx, arena);
  std::vector<Logic4Vec> arg_vals;
  for (size_t i = 1; i < expr->args.size(); ++i) {
    arg_vals.push_back(EvalExpr(expr->args[i], ctx, arena));
  }
  WarnIfArgCountMismatch(ctx, "$sformatf", fmt, arg_vals.size());
  std::string result = FormatDisplay(fmt, arg_vals, {}, nullptr, {}, &ctx);
  return StringToLogic4Vec(arena, result);
}

static Logic4Vec EvalItor(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  auto d = static_cast<double>(static_cast<int64_t>(val.ToUint64()));
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  return MakeLogic4VecVal(arena, 64, bits);
}

static Logic4Vec EvalRtoi(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  uint64_t raw_bits = val.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &raw_bits, sizeof(double));
  auto truncated = static_cast<int64_t>(d);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(truncated));
}

static Logic4Vec EvalBitstoreal(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  return MakeLogic4VecVal(arena, 64, val.ToUint64());
}

static Logic4Vec EvalRealtobits(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  uint64_t raw_bits = val.ToUint64();

  if (expr->args[0]->kind == ExprKind::kRealLiteral) {
    double d = expr->args[0]->real_val;
    std::memcpy(&raw_bits, &d, sizeof(double));
  }
  return MakeLogic4VecVal(arena, 64, raw_bits);
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
  auto val = EvalExpr(expr->args[0], ctx, arena);
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
    double d = 0.0;
    uint64_t bits = val.ToUint64();
    std::memcpy(&d, &bits, sizeof(double));
    auto f = static_cast<float>(d);
    uint32_t fbits = 0;
    std::memcpy(&fbits, &f, sizeof(float));
    return MakeLogic4VecVal(arena, 32, fbits);
  }
  if (name == "$bitstoshortreal") {
    if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
    auto val = EvalExpr(expr->args[0], ctx, arena);
    auto fbits = static_cast<uint32_t>(val.ToUint64());
    float f = 0.0f;
    std::memcpy(&f, &fbits, sizeof(float));
    auto d = static_cast<double>(f);
    uint64_t dbits = 0;
    std::memcpy(&dbits, &d, sizeof(double));
    auto result = MakeLogic4VecVal(arena, 64, dbits);
    result.is_real = true;
    return result;
  }
  if (name == "$countbits") return EvalCountbits(expr, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalIsunbounded(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  if (!expr->args.empty() && expr->args[0]->kind == ExprKind::kIdentifier) {
    bool ub = ctx.IsUnboundedParam(expr->args[0]->text);
    return MakeLogic4VecVal(arena, 1, ub ? 1 : 0);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec CastAssignSuccess(std::string_view dest_name, uint64_t src_val,
                                   SimContext& ctx, Arena& arena) {
  auto* var = ctx.FindVariable(dest_name);
  if (var) var->value = MakeLogic4VecVal(arena, var->value.width, src_val);
  return MakeLogic4VecVal(arena, 32, 1);
}

static bool TryCastEnum(std::string_view dest_name, uint64_t src_val,
                        SimContext& ctx, Arena& arena, Logic4Vec& out) {
  auto* enum_info = ctx.GetVariableEnumType(dest_name);
  if (!enum_info) return false;
  for (const auto& m : enum_info->members) {
    if (m.value == src_val) {
      out = CastAssignSuccess(dest_name, src_val, ctx, arena);
      return true;
    }
  }
  out = MakeLogic4VecVal(arena, 32, 0);
  return true;
}

static bool AreCastCompatible(const ClassTypeInfo* a, const ClassTypeInfo* b) {
  return a->IsA(b) || b->IsA(a) || a->is_interface || b->is_interface;
}

static bool TryCastClassHandle(std::string_view dest_name, uint64_t src_val,
                               const Expr* src_expr, SimContext& ctx,
                               Arena& arena, Logic4Vec& out) {
  auto dest_class = ctx.GetVariableClassType(dest_name);
  if (dest_class.empty()) return false;
  auto* dest_type = ctx.FindClassType(dest_class);
  if (!dest_type) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }

  if (src_expr && src_expr->kind == ExprKind::kIdentifier &&
      src_expr->text != "null") {
    auto src_class = ctx.GetVariableClassType(src_expr->text);
    if (!src_class.empty()) {
      auto* src_type = ctx.FindClassType(src_class);
      if (src_type && !AreCastCompatible(src_type, dest_type)) {
        out = MakeLogic4VecVal(arena, 32, 0);
        return true;
      }
    }
  }

  if (src_val == kNullClassHandle) {
    out = CastAssignSuccess(dest_name, 0, ctx, arena);
    return true;
  }
  auto* src_obj = ctx.GetClassObject(src_val);
  if (!src_obj || !src_obj->type || !src_obj->type->IsA(dest_type)) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }
  out = CastAssignSuccess(dest_name, src_val, ctx, arena);
  return true;
}

static Logic4Vec EvalCastSysFunc(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  if (expr->args.size() < 2 || !expr->args[0]) {
    return MakeLogic4VecVal(arena, 32, 0);
  }
  auto* dest_expr = expr->args[0];
  auto src = EvalExpr(expr->args[1], ctx, arena);
  uint64_t src_val = src.ToUint64();
  if (dest_expr->kind != ExprKind::kIdentifier) {
    return MakeLogic4VecVal(arena, 32, 0);
  }
  auto dest_name = dest_expr->text;
  Logic4Vec out;
  if (TryCastEnum(dest_name, src_val, ctx, arena, out)) return out;
  if (TryCastClassHandle(dest_name, src_val, expr->args[1], ctx, arena, out))
    return out;
  return CastAssignSuccess(dest_name, src_val, ctx, arena);
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
