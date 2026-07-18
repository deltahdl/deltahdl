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
    // §20.6.2: a queue or dynamic array is a dynamically sized bit-stream
    // expression. Its current bit-stream size is the live element count times
    // the per-element width, so an empty one reports 0. Both kinds keep their
    // elements in a QueueObject, so this one lookup covers each.
    if (auto* q = ctx.FindQueue(arg->text)) {
      uint64_t bits = static_cast<uint64_t>(q->elements.size()) * q->elem_width;
      return MakeLogic4VecVal(arena, 32, bits);
    }
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

// §21.6: map an integer conversion code (%d/%o/%h/%x/%b) to its radix; returns
// 0 for any other conversion letter so the caller can reject it.
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

// §21.6: decode a single text digit into its numeric value. Returns false when
// the character is not a valid hexadecimal digit, so callers can reject any
// character illegal for their radix.
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

// §21.6: validate and convert a plusarg remainder under an integer conversion
// (%d/%o/%h/%x/%b). Returns false if any character is illegal for the radix so
// the caller can store the 'bx fill the clause mandates.
static bool ParsePlusargInteger(const std::string& s, char conv, uint64_t& out,
                                bool& negative) {
  out = 0;
  negative = false;
  int base = PlusargIntegerBase(conv);
  if (base == 0) return false;
  size_t i = 0;
  if (base == 10 && i < s.size() && (s[i] == '+' || s[i] == '-')) {
    negative = (s[i] == '-');
    ++i;
  }
  if (i >= s.size()) return false;
  for (; i < s.size(); ++i) {
    int digit = 0;
    if (!DecodePlusargDigit(s[i], digit)) return false;
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

// §21.6: the destination of a $value$plusargs conversion is the named
// variable receiving the converted remainder, together with its width. Bundled
// so the conversion helpers share one entity rather than loose parameters.
struct PlusargDest {
  Variable* var;
  std::string name;
  uint32_t width;
};

// §21.6: %e/%f/%g convert the remainder to a real value, stored as its 64-bit
// IEEE pattern. An empty remainder stores zero; an unparseable remainder is
// written with 'bx.
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

// §21.6: integer conversions (%d/%o/%h/%x/%b) store the parsed magnitude. An
// empty remainder stores zero; an illegal-character remainder is written with
// 'bx; a negative value falls through MakeLogic4VecVal's two's-complement
// truncation.
static void StorePlusargInteger(Variable* var, char conv,
                                const std::string& remainder, Arena& arena,
                                uint32_t width) {
  if (remainder.empty()) {
    var->value = MakeLogic4VecVal(arena, width, 0);
    return;
  }
  uint64_t mag = 0;
  bool negative = false;
  if (!ParsePlusargInteger(remainder, conv, mag, negative)) {
    var->value = MakeAllX(arena, width);
    return;
  }
  uint64_t stored =
      negative ? static_cast<uint64_t>(-static_cast<int64_t>(mag)) : mag;
  var->value = MakeLogic4VecVal(arena, width, stored);
}

// §21.6: convert the remainder of a matching plusarg into `var` according to
// the format string's conversion code. The stored value is automatically zero-
// padded or truncated to the variable width by MakeLogic4VecVal.
static void StorePlusargValue(const PlusargDest& dest, char conv,
                              const std::string& remainder, SimContext& ctx,
                              Arena& arena) {
  if (!dest.var) return;

  // §21.6: %s performs no numeric conversion; the characters are stored as is.
  if (conv == 's') {
    dest.var->value = PackStringIntoWidth(arena, remainder, dest.width);
    return;
  }

  if (conv == 'e' || conv == 'f' || conv == 'g') {
    StorePlusargReal(dest, remainder, ctx, arena);
    return;
  }

  StorePlusargInteger(dest.var, conv, remainder, arena, dest.width);
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
  uint32_t dest_width = (var && var->value.width) ? var->value.width : 32;
  PlusargDest dest{var, var_name, dest_width};

  // §21.6: the first plusarg (in command-line order) whose prefix matches the
  // plusarg_string supplies the remainder available for conversion.
  for (const auto& arg : ctx.GetPlusArgs()) {
    if (arg.substr(0, prefix.size()) != prefix) continue;
    std::string remainder = arg.substr(prefix.size());
    StorePlusargValue(dest, conv, remainder, ctx, arena);
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

// §20.6.1: the set of built-in data-type keywords. A bare keyword given to the
// data_type form of $typename resolves to itself -- its default signing is
// implicit and therefore omitted from the string (step b).
static bool IsBuiltinTypeKeyword(std::string_view name) {
  static constexpr std::string_view kBuiltins[] = {
      "logic",   "bit",  "reg",  "byte",      "shortint", "int",    "longint",
      "integer", "time", "real", "shortreal", "realtime", "string", "chandle"};
  for (auto kw : kBuiltins) {
    if (name == kw) return true;
  }
  return false;
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
    // §20.6.1 Syntax 20-6 second form: $typename ( data_type ). A built-in
    // type keyword parses as an identifier that names no variable; its
    // resolved type name is the keyword itself.
    if (IsBuiltinTypeKeyword(arg->text)) {
      return StringToLogic4Vec(arena, std::string(arg->text));
    }
  }

  // §20.6.1 Syntax 20-6 second form with a packed dimension, e.g.
  // $typename(logic [7:0]). The parser yields a plain (msb:lsb) range select
  // over the type keyword. When the base names a built-in type -- and not a
  // variable, which would make this an expression-form part-select instead --
  // render the keyword followed by its range as unsized decimal bounds (step
  // g); the default signing stays implicit (step b).
  if (arg->kind == ExprKind::kSelect && arg->base != nullptr &&
      arg->base->kind == ExprKind::kIdentifier && arg->index != nullptr &&
      arg->index_end != nullptr && !arg->is_part_select_plus &&
      !arg->is_part_select_minus && IsBuiltinTypeKeyword(arg->base->text) &&
      ctx.FindVariable(arg->base->text) == nullptr) {
    uint64_t msb = EvalExpr(arg->index, ctx, arena).ToUint64();
    uint64_t lsb = EvalExpr(arg->index_end, ctx, arena).ToUint64();
    std::string s = std::string(arg->base->text) + "[" + std::to_string(msb) +
                    ":" + std::to_string(lsb) + "]";
    return StringToLogic4Vec(arena, s);
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

// §21.3.3: a format argument may be an unpacked array of byte, whose characters
// -- read from the array's left bound to its right bound -- form the formatting
// string. Such an array is lowered to one element variable per index rather
// than a single packed value, so EvalStringArg cannot decode it; reconstruct
// the string from the element variables here. Returns false when the argument
// is not a fixed unpacked byte array, leaving the packed-value path in charge.
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

// §21.3.3 N10: a format argument may be supplied as a string literal or as any
// expression whose content encodes the formatting string -- an integral or
// string value via its packed bytes, or an unpacked array of byte via its
// elements. Shared with eval_systask_io.cpp.
std::string ResolveFormatArg(const Expr* arg, SimContext& ctx, Arena& arena) {
  if (arg && arg->kind == ExprKind::kStringLiteral) {
    return ExtractFormatString(arg);
  }
  std::string from_array;
  if (TryFormatArgFromByteArray(arg, ctx, from_array)) return from_array;
  return EvalStringArg(arg, ctx, arena);
}

// Outcome of scanning one '%'-introduced specifier.
enum class SpecifierScan : std::uint8_t {
  kLiteralPercent,
  kTruncated,
  kComplete
};

// §21.3.3: scan the specifier that begins at fmt[i] (which is '%'). Advances
// `i` past the consumed characters and reports whether the specifier consumes
// an argument value (%m/%l and %% do not). Mirrors the control flow of the
// caller: a `%%` literal advances one and consumes nothing; a specifier whose
// body runs off the end of the string is reported truncated.
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

// §21.3.3: counts %-introduced specifiers that consume an argument value,
// excluding %% literals and %m/%l self-supplied specifiers.
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
  std::string result = FormatDisplay(fmt, arg_vals, {.ctx = &ctx});
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

// Flatten a parameter reference into the instance-qualified name the lowerer
// registers a parameter under. A simple ps_parameter_identifier is just its
// text; a hierarchical_parameter_identifier parses as a member-access chain
// (e.g. sub.P -> lhs "sub", rhs "P") whose segments join with dots, matching
// the "inst_prefix.name" key LowerParams builds.
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

static Logic4Vec EvalIsunbounded(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  // §20.6.3: $isunbounded reports whether its parameter argument holds the
  // unbounded value $. Syntax 20-8 admits both a simple and a hierarchical
  // parameter identifier, so accept a member-access operand (sub.P) alongside a
  // bare identifier by resolving either to its registered name.
  if (!expr->args.empty()) {
    std::string name;
    if (FlattenParamRefName(expr->args[0], name)) {
      bool ub = ctx.IsUnboundedParam(name);
      return MakeLogic4VecVal(arena, 1, ub ? 1 : 0);
    }
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

// Static-type screen for a $cast to a class handle: if the source expression
// names a typed class variable whose declared type is not cast-compatible with
// the destination type, the cast fails outright.
static bool SrcClassTypeIncompatible(const Expr* src_expr,
                                     const ClassTypeInfo* dest_type,
                                     SimContext& ctx) {
  if (!src_expr || src_expr->kind != ExprKind::kIdentifier ||
      src_expr->text == "null") {
    return false;
  }
  auto src_class = ctx.GetVariableClassType(src_expr->text);
  if (src_class.empty()) return false;
  auto* src_type = ctx.FindClassType(src_class);
  return src_type && !AreCastCompatible(src_type, dest_type);
}

// §6.24.1 $cast: one dynamic cast request names a destination variable
// (dest_name) and the source it is cast from (its run-time handle src_val and
// the originating expression src_expr used for the static-type screen).
struct CastRequest {
  std::string_view dest_name;
  uint64_t src_val;
  const Expr* src_expr;
};

static bool TryCastClassHandle(const CastRequest& req, SimContext& ctx,
                               Arena& arena, Logic4Vec& out) {
  auto dest_class = ctx.GetVariableClassType(req.dest_name);
  if (dest_class.empty()) return false;
  auto* dest_type = ctx.FindClassType(dest_class);
  if (!dest_type) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }

  if (SrcClassTypeIncompatible(req.src_expr, dest_type, ctx)) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }

  if (req.src_val == kNullClassHandle) {
    out = CastAssignSuccess(req.dest_name, 0, ctx, arena);
    return true;
  }
  auto* src_obj = ctx.GetClassObject(req.src_val);
  if (!src_obj || !src_obj->type || !src_obj->type->IsA(dest_type)) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }
  out = CastAssignSuccess(req.dest_name, req.src_val, ctx, arena);
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
  CastRequest cast_req{dest_name, src_val, expr->args[1]};
  if (TryCastClassHandle(cast_req, ctx, arena, out)) return out;
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
