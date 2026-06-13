#include <algorithm>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <iterator>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/coverage_control.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
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

static std::string ExtractStrArg(const Expr* arg) {
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
    case 'd': base = 10; break;
    case 'o': base = 8; break;
    case 'h':
    case 'x': base = 16; break;
    case 'b': base = 2; break;
    default: return false;
  }
  size_t i = 0;
  if (base == 10 && i < s.size() && (s[i] == '+' || s[i] == '-')) {
    negative = (s[i] == '-');
    ++i;
  }
  if (i >= s.size()) return false;
  for (; i < s.size(); ++i) {
    char c = s[i];
    int digit;
    if (c >= '0' && c <= '9') digit = c - '0';
    else if (c >= 'a' && c <= 'f') digit = c - 'a' + 10;
    else if (c >= 'A' && c <= 'F') digit = c - 'A' + 10;
    else return false;
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

// §21.6: convert the remainder of a matching plusarg into `var` according to the
// format string's conversion code. The stored value is automatically zero-
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
  uint32_t w = var->width;

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

// §21.3.3: the format argument may be a string literal or an expression whose
// content is interpreted as the formatting string. Literal forms are taken
// verbatim from the token text; non-literal forms have their packed-byte value
// decoded back into a std::string here.
static std::string ResolveFormatArg(const Expr* arg, SimContext& ctx,
                                    Arena& arena);

// §21.3.3: counts %-introduced specifiers that consume an argument value,
// excluding %% literals and %m/%l self-supplied specifiers.
static size_t CountConsumingSpecifiers(const std::string& fmt) {
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
static void WarnIfArgCountMismatch(SimContext& ctx, std::string_view task_name,
                                   const std::string& fmt, size_t supplied) {
  size_t required = CountConsumingSpecifiers(fmt);
  if (supplied == required) return;
  std::string msg = std::string(task_name) +
                    ": format-specifier count (" + std::to_string(required) +
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

// §21.3.3: shared output-string builder used by $swrite{,b,h,o} and $sformat.
// `args` are the unevaluated argument expressions following the output
// variable; `default_radix` is the format-specifier letter applied to any
// bare expression argument when no embedded format string drives it.
static std::string BuildStringTaskOutput(const std::vector<Expr*>& args,
                                         char default_radix, SimContext& ctx,
                                         Arena& arena) {
  std::string out;
  for (size_t i = 0; i < args.size(); ++i) {
    const Expr* a = args[i];
    if (a == nullptr) {
      out += ' ';
      continue;
    }
    if (a->kind == ExprKind::kStringLiteral) {
      std::string fmt = ExtractFormatString(a);
      std::vector<Logic4Vec> vals;
      while (i + 1 < args.size() && args[i + 1] != nullptr &&
             args[i + 1]->kind != ExprKind::kStringLiteral) {
        vals.push_back(EvalExpr(args[++i], ctx, arena));
      }
      out += FormatDisplay(fmt, vals, {}, nullptr, {}, &ctx);
      continue;
    }
    auto val = EvalExpr(a, ctx, arena);
    char spec = val.is_string ? 's' : default_radix;
    char fmt_buf[3] = {'%', spec, 0};
    out += FormatDisplay(fmt_buf, {val}, {}, nullptr, {}, &ctx);
  }
  return out;
}

// §21.3.3 N6: $swrite/$swriteb/$swriteh/$swriteo take an output variable as
// the first argument and write the formatted result into it under string-
// literal assignment-to-variable rules. The b/h/o suffix selects the default
// radix for bare expression arguments per §21.3.2.
static Logic4Vec EvalSwriteFamily(const Expr* expr, SimContext& ctx,
                                  Arena& arena, std::string_view name) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  Variable* dst = nullptr;
  if (expr->args[0] && expr->args[0]->kind == ExprKind::kIdentifier) {
    dst = ctx.FindVariable(expr->args[0]->text);
  }

  // The suffix character ('\0' / b / h / o) becomes the default radix letter
  // for bare expression arguments. Without a suffix, decimal is the default.
  char default_radix = 'd';
  if (name.size() >= 1) {
    char back = name.back();
    if (back == 'b' || back == 'h' || back == 'o') default_radix = back;
  }

  std::vector<Expr*> rest(expr->args.begin() + 1, expr->args.end());
  std::string output =
      BuildStringTaskOutput(rest, default_radix, ctx, arena);
  if (dst) {
    // §5.9 / §21.3.3 N7: writing via StringToLogic4Vec packs the leftmost
    // character at the high byte position, giving left-bound to right-bound
    // ordering across the destination's bits.
    dst->value = StringToLogic4Vec(arena, output);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

// §21.3.3 N9: $sformat always interprets its second argument, and only its
// second argument, as the format string; following arguments fill its
// specifiers in order and are never re-interpreted as format strings.
static Logic4Vec EvalSformatTask(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 1, 0);
  Variable* dst = nullptr;
  if (expr->args[0] && expr->args[0]->kind == ExprKind::kIdentifier) {
    dst = ctx.FindVariable(expr->args[0]->text);
  }
  std::string fmt = ResolveFormatArg(expr->args[1], ctx, arena);
  std::vector<Logic4Vec> vals;
  for (size_t i = 2; i < expr->args.size(); ++i) {
    vals.push_back(EvalExpr(expr->args[i], ctx, arena));
  }
  WarnIfArgCountMismatch(ctx, "$sformat", fmt, vals.size());
  std::string out = FormatDisplay(fmt, vals, {}, nullptr, {}, &ctx);
  if (dst) dst->value = StringToLogic4Vec(arena, out);
  return MakeLogic4VecVal(arena, 1, 0);
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

// Build an all-x integer result. §20.7 calls for 'x whenever a query has no
// well-defined answer (a dimensionless first argument or an out-of-range
// dimension index).
static Logic4Vec MakeUnknownInt(Arena& arena, uint32_t width) {
  auto vec = MakeLogic4Vec(arena, width);
  uint64_t mask = (width < 64) ? ((uint64_t{1} << width) - 1) : ~uint64_t{0};
  if (vec.nwords > 0) {
    vec.words[0].aval = mask;
    vec.words[0].bval = mask;
  }
  return vec;
}

// Bounds of a single array dimension, as the array query functions report them.
struct QueryDimBounds {
  int64_t left = 0;
  int64_t right = 0;
  int64_t low = 0;
  int64_t high = 0;
  int64_t increment = 1;
  int64_t size = 0;
  bool low_high_unknown = false;  // $low/$high are 'x for an empty assoc array
};

Logic4Vec EvalArrayQuerySysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                std::string_view name) {
  const Expr* arg0 = expr->args.empty() ? nullptr : expr->args[0];

  // Classify the first argument's outermost (slowest varying) dimension.
  AssocArrayObject* assoc = nullptr;
  QueueObject* queue = nullptr;
  const ArrayInfo* arr = nullptr;
  if (arg0 && arg0->kind == ExprKind::kIdentifier) {
    assoc = ctx.FindAssocArray(arg0->text);
    queue = ctx.FindQueue(arg0->text);
    arr = ctx.FindArrayInfo(arg0->text);
  }
  bool dynamic_outer =
      queue != nullptr || (arr != nullptr && (arr->is_dynamic || arr->is_queue));
  bool has_unpacked = assoc != nullptr || queue != nullptr || arr != nullptr;

  // Width of the packed element dimension (the [n-1:0] of an integer type).
  uint32_t elem_width = 32;
  bool is_real = false;
  bool is_string = false;
  if (assoc) {
    elem_width = assoc->elem_width;
  } else if (queue) {
    elem_width = queue->elem_width;
  } else if (arr) {
    elem_width = arr->elem_width;
  } else if (arg0 && arg0->kind == ExprKind::kIdentifier &&
             ctx.IsStringVariable(arg0->text)) {
    // §20.7: a string is a nonarray type that is equivalent to a simple bit
    // vector, so it always contributes exactly one packed dimension regardless
    // of how many characters it currently holds.
    is_string = true;
  } else if (arg0) {
    auto val = EvalExpr(arg0, ctx, arena);
    elem_width = val.width;
    is_real = val.is_real;
  }

  // A simple bit-vector type (string included) contributes one packed
  // dimension; a real (or any other nonvector) type contributes none.
  uint32_t packed_dims = (is_string || (elem_width > 0 && !is_real)) ? 1 : 0;
  uint32_t unpacked_dims = has_unpacked ? 1 : 0;
  uint32_t total_dims = packed_dims + unpacked_dims;

  if (name == "$dimensions")
    return MakeLogic4VecVal(arena, 32, total_dims);
  if (name == "$unpacked_dimensions")
    return MakeLogic4VecVal(arena, 32, unpacked_dims);

  // §20.7: 'x when the first argument has no dimensions ($dimensions would be
  // 0) or when the optional dimension index is out of range.
  if (total_dims == 0) return MakeUnknownInt(arena, 32);
  uint32_t dim = 1;
  if (expr->args.size() > 1)
    dim = static_cast<uint32_t>(EvalExpr(expr->args[1], ctx, arena).ToUint64());
  if (dim < 1 || dim > total_dims) return MakeUnknownInt(arena, 32);

  // Dimension 1 is the slowest varying. When an unpacked dimension is present
  // it is dimension 1 and the packed element dimension (if any) is dimension 2;
  // otherwise the packed dimension is dimension 1.
  bool query_unpacked = has_unpacked && dim == 1;

  QueryDimBounds q;
  if (query_unpacked && assoc) {
    // Associative array dimension with an integral index type.
    uint32_t iw = assoc->index_width ? assoc->index_width : 32;
    q.left = 0;
    q.right = (iw >= 64) ? static_cast<int64_t>(~uint64_t{0})
                         : static_cast<int64_t>((uint64_t{1} << iw) - 1);
    q.increment = -1;
    q.size = assoc->Size();
    if (assoc->int_data.empty()) {
      q.low_high_unknown = true;
    } else {
      q.low = assoc->int_data.begin()->first;
      q.high = assoc->int_data.rbegin()->first;
    }
  } else if (query_unpacked && dynamic_outer) {
    // Queue or dynamic array dimension: indices run 0 .. size-1, descending.
    int64_t count =
        queue ? static_cast<int64_t>(queue->elements.size())
              : static_cast<int64_t>(arr ? arr->size : 0);
    q.left = 0;
    q.right = count - 1;  // -1 when the dimension is currently empty
    q.low = 0;
    q.high = count - 1;
    q.increment = -1;
    q.size = count;
  } else if (query_unpacked && arr) {
    // Fixed-size unpacked dimension with declared bounds.
    int64_t lo = arr->lo;
    int64_t hi = arr->lo + static_cast<int64_t>(arr->size) - 1;
    q.left = arr->is_descending ? hi : lo;
    q.right = arr->is_descending ? lo : hi;
    q.low = lo;
    q.high = hi;
    q.size = arr->size;
    q.increment = (q.left >= q.right) ? 1 : -1;
  } else {
    // Packed element dimension [elem_width-1 : 0].
    q.left = static_cast<int64_t>(elem_width) - 1;
    q.right = 0;
    q.low = 0;
    q.high = static_cast<int64_t>(elem_width) - 1;
    q.size = elem_width;
    q.increment = (q.left >= q.right) ? 1 : -1;
  }

  auto as_int = [&](int64_t v) {
    return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(v));
  };
  if (name == "$left") return as_int(q.left);
  if (name == "$right") return as_int(q.right);
  if (name == "$increment") return as_int(q.increment);
  if (name == "$low")
    return q.low_high_unknown ? MakeUnknownInt(arena, 32) : as_int(q.low);
  if (name == "$high")
    return q.low_high_unknown ? MakeUnknownInt(arena, 32) : as_int(q.high);
  return as_int(q.size);  // $size
}

// §20.15.6 Table 20-11 status code values returned through the trailing
// `status` output argument of every stochastic-analysis queue task and
// function. Value 7 ("not enough memory, cannot create queue") is defined by
// the table but has no deterministic trigger in the model, so nothing emits
// it.
enum QueueStatus : uint64_t {
  kQOk = 0,                 // OK
  kQFullCannotAdd = 1,      // queue full, cannot add
  kQUndefinedId = 2,        // undefined q_id
  kQEmptyCannotRemove = 3,  // queue empty, cannot remove
  kQUnsupportedType = 4,    // unsupported queue type, cannot create
  kQNonPositiveLength = 5,  // specified length <= 0, cannot create
  kQDuplicateId = 6,        // duplicate q_id, cannot create
};

// Read an argument as a signed value, sign-extending from its own width so a
// negative max_length is recognized as such (Table 20-11 status 5 keys on
// length <= 0).
static int64_t QueueSignedArg(const Logic4Vec& v) {
  uint64_t raw = v.ToUint64();
  uint32_t w = v.width;
  if (w == 0 || w >= 64) return static_cast<int64_t>(raw);
  uint64_t sign_bit = 1ull << (w - 1);
  if (raw & sign_bit) raw |= ~((1ull << w) - 1);
  return static_cast<int64_t>(raw);
}

// §20.15.6: deliver the resolved status code into the queue task's `status`
// output argument, which every queue task and function returns.
static void WriteQueueStatus(const Expr* status_arg, uint64_t status,
                             SimContext& ctx, Arena& arena) {
  if (!status_arg || status_arg->kind != ExprKind::kIdentifier) return;
  auto* var = ctx.FindVariable(status_arg->text);
  if (var) var->value = MakeLogic4VecVal(arena, var->value.width, status);
}

// §20.15.3: write an integer value back through one of $q_remove's output
// arguments (job_id, inform_id), keeping the destination variable's own width.
static void WriteQueueOutput(const Expr* out_arg, uint64_t value,
                             SimContext& ctx, Arena& arena) {
  if (!out_arg || out_arg->kind != ExprKind::kIdentifier) return;
  auto* var = ctx.FindVariable(out_arg->text);
  if (var) var->value = MakeLogic4VecVal(arena, var->value.width, value);
}

// §20.15.6: resolve and report the Table 20-11 status code for each
// stochastic-analysis queue task/function. The queue type/capacity validated
// at $q_initialize and the occupancy tracked across $q_add/$q_remove supply
// the error conditions. $q_remove additionally returns its removed entry's
// job_id/inform_id outputs (§20.15.3), $q_full its fullness result (§20.15.4),
// and $q_exam its requested statistic (§20.15.5) through the q_stat_value
// output.
static Logic4Vec EvalStochasticQueue(const Expr* expr, SimContext& ctx,
                                     Arena& arena, std::string_view name) {
  auto& queues = ctx.StochasticQueues();
  const auto& args = expr->args;

  if (name == "$q_initialize") {
    if (args.size() < 4) return MakeLogic4VecVal(arena, 32, 0);
    uint64_t q_id = EvalExpr(args[0], ctx, arena).ToUint64();
    int64_t q_type = QueueSignedArg(EvalExpr(args[1], ctx, arena));
    int64_t max_length = QueueSignedArg(EvalExpr(args[2], ctx, arena));
    uint64_t status;
    if (q_type != 1 && q_type != 2) {
      status = kQUnsupportedType;
    } else if (max_length <= 0) {
      status = kQNonPositiveLength;
    } else if (queues.count(q_id)) {
      status = kQDuplicateId;
    } else {
      queues[q_id] = StochasticQueue{q_type, max_length, 0};
      status = kQOk;
    }
    WriteQueueStatus(args[3], status, ctx, arena);
    return MakeLogic4VecVal(arena, 32, status);
  }

  if (name == "$q_add") {
    if (args.size() < 4) return MakeLogic4VecVal(arena, 32, 0);
    uint64_t q_id = EvalExpr(args[0], ctx, arena).ToUint64();
    auto it = queues.find(q_id);
    uint64_t status;
    if (it == queues.end()) {
      status = kQUndefinedId;
    } else if (static_cast<int64_t>(it->second.count) >=
               it->second.max_length) {
      status = kQFullCannotAdd;
    } else {
      // Retain the entry's identifiers so §20.15.3 $q_remove can return them;
      // the inform_id holds whatever value $q_add was handed (its meaning is
      // user-defined).
      uint64_t job_id = EvalExpr(args[1], ctx, arena).ToUint64();
      uint64_t inform_id = EvalExpr(args[2], ctx, arena).ToUint64();
      // §20.15.5: stamp the arrival time and fold it into the queue's activity
      // statistics so $q_exam can report mean interarrival time, peak occupancy
      // and wait times.
      uint64_t now = ctx.CurrentTime().ticks;
      auto& q = it->second;
      q.entries.push_back(StochasticQueueEntry{job_id, inform_id, now});
      if (q.arrivals == 0) q.first_arrival_tick = now;
      q.last_arrival_tick = now;
      ++q.arrivals;
      ++q.count;
      if (q.count > q.max_count) q.max_count = q.count;
      status = kQOk;
    }
    WriteQueueStatus(args[3], status, ctx, arena);
    return MakeLogic4VecVal(arena, 32, status);
  }

  if (name == "$q_remove") {
    // §20.15.3 $q_remove(q_id, job_id, inform_id, status): take an entry off
    // the queue selected by q_id (an integer input) and report the removed
    // entry's identifiers through the job_id and inform_id outputs.
    if (args.size() < 4) return MakeLogic4VecVal(arena, 32, 0);
    uint64_t q_id = EvalExpr(args[0], ctx, arena).ToUint64();
    auto it = queues.find(q_id);
    uint64_t status;
    if (it == queues.end()) {
      status = kQUndefinedId;
    } else if (it->second.count == 0) {
      status = kQEmptyCannotRemove;
    } else {
      // Choose the entry per the discipline fixed at $q_initialize: q_type 2
      // (LIFO) returns the most recently added entry, otherwise q_type 1
      // (FIFO) returns the oldest. $q_add always appends to the back.
      auto& q = it->second;
      StochasticQueueEntry entry;
      if (q.q_type == 2) {
        entry = q.entries.back();
        q.entries.pop_back();
      } else {
        entry = q.entries.front();
        q.entries.pop_front();
      }
      --q.count;
      // §20.15.5: a removed entry's residence time completes a wait sample,
      // feeding the shortest-ever and average wait-time statistics reported by
      // $q_exam.
      uint64_t now = ctx.CurrentTime().ticks;
      uint64_t wait = now >= entry.arrival_tick ? now - entry.arrival_tick : 0;
      if (q.departures == 0 || wait < q.shortest_wait) q.shortest_wait = wait;
      q.total_wait += wait;
      ++q.departures;
      WriteQueueOutput(args[1], entry.job_id, ctx, arena);
      WriteQueueOutput(args[2], entry.inform_id, ctx, arena);
      status = kQOk;
    }
    WriteQueueStatus(args[3], status, ctx, arena);
    return MakeLogic4VecVal(arena, 32, status);
  }

  if (name == "$q_full") {
    // §20.15.4: $q_full checks whether the queue named by q_id has room for
    // another entry, returning 1 when it is full and 0 when it is not. A queue
    // is full once its occupancy reaches the capacity fixed at $q_initialize.
    // The trailing status reports the operation outcome (§20.15.6); the only
    // error condition that applies is an undefined q_id.
    if (args.size() < 2) return MakeLogic4VecVal(arena, 32, 0);
    uint64_t q_id = EvalExpr(args[0], ctx, arena).ToUint64();
    auto it = queues.find(q_id);
    WriteQueueStatus(args[1], it == queues.end() ? kQUndefinedId : kQOk, ctx,
                     arena);
    uint64_t full = (it != queues.end() &&
                     static_cast<int64_t>(it->second.count) >=
                         it->second.max_length)
                        ? 1u
                        : 0u;
    return MakeLogic4VecVal(arena, 32, full);
  }

  if (name == "$q_exam") {
    // §20.15.5 $q_exam(q_id, q_stat_code, q_stat_value, status): report a
    // statistic about activity on the queue named by q_id. The q_stat_code
    // selects which statistic is delivered through the q_stat_value output, per
    // Table 20-10. An undefined q_id is the only applicable error (§20.15.6).
    if (args.size() < 4) return MakeLogic4VecVal(arena, 32, 0);
    uint64_t q_id = EvalExpr(args[0], ctx, arena).ToUint64();
    auto it = queues.find(q_id);
    if (it == queues.end()) {
      WriteQueueStatus(args[3], kQUndefinedId, ctx, arena);
      return MakeLogic4VecVal(arena, 32, kQUndefinedId);
    }
    const auto& q = it->second;
    int64_t code = QueueSignedArg(EvalExpr(args[1], ctx, arena));
    uint64_t now = ctx.CurrentTime().ticks;
    uint64_t value = 0;
    switch (code) {
      case 1:  // Current queue length.
        value = q.count;
        break;
      case 2:  // Mean interarrival time: total span between the first and last
               // arrival divided by the number of gaps between arrivals.
        value = q.arrivals > 1
                    ? (q.last_arrival_tick - q.first_arrival_tick) /
                          (q.arrivals - 1)
                    : 0;
        break;
      case 3:  // Maximum queue length ever reached.
        value = q.max_count;
        break;
      case 4:  // Shortest wait time ever, across removed entries.
        value = q.departures ? q.shortest_wait : 0;
        break;
      case 5:  // Longest wait among entries still queued: the oldest entry is at
               // the front, as $q_add appends in arrival order.
        value = q.entries.empty()
                    ? 0
                    : (now >= q.entries.front().arrival_tick
                           ? now - q.entries.front().arrival_tick
                           : 0);
        break;
      case 6:  // Average wait time over removed entries.
        value = q.departures ? q.total_wait / q.departures : 0;
        break;
      default:
        value = 0;
        break;
    }
    WriteQueueOutput(args[2], value, ctx, arena);
    WriteQueueStatus(args[3], kQOk, ctx, arena);
    return MakeLogic4VecVal(arena, 32, kQOk);
  }

  return MakeLogic4VecVal(arena, 32, 0);
}

// §40.3.2.1: $coverage_control(control_constant, coverage_type, scope_def,
// modules_or_instance) performs the control action named by its first argument
// over the scope named by its fourth and returns one of the §40.3.1 status
// values. The action is applied to the simulation's coverage-control state.
static Logic4Vec EvalCoverageControl(const Expr* expr, SimContext& ctx,
                                     Arena& arena) {
  auto status_vec = [&](CoverageStatus status) {
    return MakeLogic4VecVal(arena, 32,
                            static_cast<uint32_t>(static_cast<int>(status)));
  };
  // A control constant outside the §40.3.1 set (or a missing one) is a bad
  // argument, reported as `SV_COV_ERROR.
  if (expr->args.empty()) return status_vec(CoverageStatus::Error);
  int control_value =
      static_cast<int>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  CoverageControl control;
  if (!CoverageControlFromInt(control_value, &control)) {
    return status_vec(CoverageStatus::Error);
  }
  // The fourth argument names the module definition or instance. When given as a
  // string literal it is used directly; otherwise the scope is left empty.
  std::string scope;
  if (expr->args.size() > 3 &&
      expr->args[3]->kind == ExprKind::kStringLiteral) {
    scope = ExtractStrArg(expr->args[3]);
  }
  return status_vec(ctx.GetCoverageControlState().Control(control, scope));
}

// §40.3.2.2: $coverage_get_max(coverage_type, scope_def, modules_or_instance)
// returns the value representing 100% coverage for the given coverage type over
// the named hierarchy — the sum of all coverable items of that type. The value
// is a property of the design and stays constant for the whole simulation. The
// integer result is one of the §40.3.1 status values (`SV_COV_ERROR for bad
// arguments, `SV_COV_NOCOV when no coverage is available, `SV_COV_OVERFLOW when
// the count is too large to represent) or a positive maximum coverage number.
static Logic4Vec EvalCoverageGetMax(const Expr* expr, SimContext& ctx,
                                    Arena& arena) {
  auto int_vec = [&](int value) {
    return MakeLogic4VecVal(arena, 32, static_cast<uint32_t>(value));
  };
  // The first argument selects the coverage type; without it the arguments are
  // incorrect, reported as `SV_COV_ERROR.
  if (expr->args.empty()) {
    return int_vec(static_cast<int>(CoverageStatus::Error));
  }
  int coverage_type =
      static_cast<int>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  // The third argument names the module definition or instance, as the scope is
  // specified per $coverage_control() (§40.3.2.1). A string literal is used
  // directly; otherwise the scope is left empty.
  std::string scope;
  if (expr->args.size() > 2 &&
      expr->args[2]->kind == ExprKind::kStringLiteral) {
    scope = ExtractStrArg(expr->args[2]);
  }
  return int_vec(ctx.GetCoverageControlState().CoverageMax(scope, coverage_type));
}

Logic4Vec EvalVerifSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           std::string_view name) {

  if (name == "$sampled") {
    if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
    return EvalExpr(expr->args[0], ctx, arena);
  }
  if (name == "$past") {
    if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
    return EvalExpr(expr->args[0], ctx, arena);
  }
  if (name == "$rose" || name == "$fell" || name == "$stable" ||
      name == "$changed") {
    return MakeLogic4VecVal(arena, 1, 0);
  }

  // §16.9.4: $past_gclk(v) is defined as $past(v,,,@$global_clock) and
  // $future_gclk(v) is the value of v sampled at the next global clock tick;
  // both yield the (sampled) value of their argument.
  if (name == "$past_gclk" || name == "$future_gclk") {
    if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
    return EvalExpr(expr->args[0], ctx, arena);
  }

  // §16.9.4: the global clocking value-change functions ($rose_gclk,
  // $fell_gclk, $stable_gclk, $changed_gclk and the future $rising_gclk,
  // $falling_gclk, $steady_gclk, $changing_gclk) each return a 1-bit Boolean.
  if (name.ends_with("_gclk")) {
    return MakeLogic4VecVal(arena, 1, 0);
  }

  if (name.starts_with("$assert")) return MakeLogic4VecVal(arena, 1, 0);

  if (name == "$coverage_control") return EvalCoverageControl(expr, ctx, arena);

  if (name == "$coverage_get_max") return EvalCoverageGetMax(expr, ctx, arena);

  if (name.starts_with("$coverage")) return MakeLogic4VecVal(arena, 32, 0);

  if (name.starts_with("$q_"))
    return EvalStochasticQueue(expr, ctx, arena, name);

  return MakeLogic4VecVal(arena, 32, 0);
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

static std::string EvalStringArg(const Expr* arg, SimContext& ctx,
                                 Arena& arena);

static Logic4Vec EvalFopen(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  // §21.3.1 admits a filename / type argument that is a string literal, a
  // string-typed variable, or an integral value whose bytes encode the
  // characters; EvalStringArg handles all three forms.
  std::string filename = EvalStringArg(expr->args[0], ctx, arena);
  // §21.3.1: omitting the type argument requests a multichannel descriptor;
  // supplying it requests a single 32-bit file descriptor.
  if (expr->args.size() < 2) {
    uint32_t mcd = ctx.OpenMcd(filename);
    return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(mcd));
  }
  std::string mode = EvalStringArg(expr->args[1], ctx, arena);
  uint32_t fd = ctx.OpenFile(filename, mode);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(fd));
}

static Logic4Vec EvalFclose(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  auto descriptor =
      static_cast<uint32_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  ctx.CloseFile(descriptor);
  return MakeLogic4VecVal(arena, 1, 0);
}

// Determines whether a system-task name names a §21.3.2 file-output task and,
// if so, returns the radix character for any base-specific suffix (b/h/o).
// Returns '\0' for the default ($fdisplay, $fwrite, $fstrobe, $fmonitor),
// 'b'/'h'/'o' for the suffixed variants, and '?' if the name is not in the set.
static char FileOutputSuffix(std::string_view name) {
  auto match = [&](std::string_view base) -> char {
    if (name == base) return '\0';
    if (name.size() == base.size() + 1 && name.substr(0, base.size()) == base) {
      char c = name.back();
      if (c == 'b' || c == 'h' || c == 'o') return c;
    }
    return '?';
  };
  for (auto base : {"$fdisplay", "$fwrite", "$fstrobe", "$fmonitor"}) {
    char s = match(base);
    if (s != '?') return s;
  }
  return '?';
}

static bool IsFileOutputTask(std::string_view name) {
  return FileOutputSuffix(name) != '?';
}

// Routes formatted output to every FILE* selected by a descriptor argument.
// An fd has its MSB set and refers to a single open file (or to STDIN/STDOUT/
// STDERR); an mcd has its MSB clear and may select multiple channels at once
// by setting their channel bits (§21.3.1, §21.3.2).
static std::vector<FILE*> ResolveOutputTargets(uint32_t descriptor,
                                               SimContext& ctx) {
  if ((descriptor & SimContext::kFdMsb) != 0) {
    FILE* fp = ctx.GetFileHandle(descriptor);
    if (fp == nullptr) return {};
    return {fp};
  }
  return ctx.GetMcdFiles(descriptor);
}

static Logic4Vec EvalFdisplayWrite(const Expr* expr, SimContext& ctx,
                                   Arena& arena, std::string_view name) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  auto descriptor =
      static_cast<uint32_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  auto targets = ResolveOutputTargets(descriptor, ctx);
  if (targets.empty()) return MakeLogic4VecVal(arena, 1, 0);

  char suffix = FileOutputSuffix(name);
  bool is_display_family =
      name.rfind("$fdisplay", 0) == 0 || name.rfind("$fstrobe", 0) == 0 ||
      name.rfind("$fmonitor", 0) == 0;

  std::string fmt;
  std::vector<Logic4Vec> arg_vals;
  for (size_t i = 1; i < expr->args.size(); ++i) {
    auto val = EvalExpr(expr->args[i], ctx, arena);
    if (i == 1 && expr->args[i]->kind == ExprKind::kStringLiteral) {
      fmt = ExtractFormatString(expr->args[i]);
    } else {
      arg_vals.push_back(val);
    }
  }
  std::string output;
  if (!fmt.empty()) {
    output = FormatDisplay(fmt, arg_vals, {}, nullptr, {}, &ctx);
  } else if (suffix != '\0') {
    // §21.3.2 derives b/h/o radix from the task-name suffix when no format
    // string is supplied.
    char fmt_buf[3] = {'%', suffix, 0};
    output = FormatDisplay(fmt_buf, arg_vals, {}, nullptr, {}, &ctx);
  }
  for (FILE* fp : targets) {
    std::fputs(output.c_str(), fp);
    if (is_display_family) std::fputc('\n', fp);
    std::fflush(fp);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

// §21.4: a number in the load file carries neither a length nor a base; the
// task name fixes the radix (binary for $readmemb, hexadecimal for $readmemh).
// The unknown value (x), the high-impedance value (z), and underscores may
// appear within a number, so the token is parsed into a 4-state element value
// rather than a plain integer. Underscores are discarded separators; x/z
// preserve their per-bit nature in the loaded word.
static Logic4Vec ParseMemNumber(Arena& arena, const std::string& tok,
                                bool is_hex, uint32_t width) {
  std::vector<std::pair<bool, bool>> bits;  // (aval, bval), least bit first
  int per_char = is_hex ? 4 : 1;
  for (auto it = tok.rbegin(); it != tok.rend(); ++it) {
    char c = *it;
    if (c == '_') continue;
    uint8_t aval = 0;
    uint8_t bval = 0;
    if (c == 'x' || c == 'X') {
      aval = is_hex ? 0xF : 0x1;
      bval = aval;
    } else if (c == 'z' || c == 'Z' || c == '?') {
      bval = is_hex ? 0xF : 0x1;
    } else {
      int digit = -1;
      if (c >= '0' && c <= '9') {
        digit = c - '0';
      } else if (c >= 'a' && c <= 'f') {
        digit = c - 'a' + 10;
      } else if (c >= 'A' && c <= 'F') {
        digit = c - 'A' + 10;
      }
      if (digit < 0) continue;
      aval = static_cast<uint8_t>(digit);
    }
    for (int b = 0; b < per_char; ++b) {
      bits.push_back({(aval >> b) & 1, (bval >> b) & 1});
    }
  }
  auto vec = MakeLogic4Vec(arena, width);
  for (uint32_t i = 0; i < width && i < bits.size(); ++i) {
    if (bits[i].first) vec.words[i / 64].aval |= uint64_t{1} << (i % 64);
    if (bits[i].second) vec.words[i / 64].bval |= uint64_t{1} << (i % 64);
  }
  return vec;
}

// §21.4.2: a 2-state destination — such as an int or bit vector, or an
// enumerated type with a 2-state base — cannot hold x or z, so any unknown or
// high-impedance bit read from the load file is turned into 0. In the 4-state
// encoding an x bit is aval=bval=1 and a z bit is aval=0/bval=1; clearing every
// bit whose bval is set and then dropping bval reduces both to a plain 0, while
// 0 and 1 bits are left unchanged. Reading otherwise proceeds exactly as for a
// 4-state element type.
static void CoerceToTwoState(Logic4Vec& v) {
  for (uint32_t i = 0; i < v.nwords; ++i) {
    v.words[i].aval &= ~v.words[i].bval;
    v.words[i].bval = 0;
  }
}

// §21.4.2: file data for an enumerated destination is the numeric value of one
// of the type's elements (see 6.19). A number matching no element is out of
// range for the type.
static bool EnumValueInRange(const EnumTypeInfo* info, const Logic4Vec& v) {
  uint64_t val = v.ToUint64();
  for (const auto& m : info->members) {
    if (m.value == val) return true;
  }
  return false;
}

// §21.4: walks a memory-load text file in file order. White space and both
// comment styles separate tokens. Each @-address (a hexadecimal index with no
// intervening white space) is handed to on_addr; each unsized number is handed
// to on_word (see ParseMemNumber for its grammar). Either callback returns
// false to abort the scan (an out-of-range address, for example).
template <class AddrFn, class WordFn>
static void ScanMemFile(const std::string& content, AddrFn on_addr,
                        WordFn on_word) {
  auto is_space = [](char c) {
    return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' ||
           c == '\v';
  };
  size_t pos = 0;
  size_t n = content.size();
  while (pos < n) {
    char c = content[pos];
    if (is_space(c)) {
      ++pos;
      continue;
    }
    // §21.4: both comment forms are permitted between numbers.
    if (c == '/' && pos + 1 < n && content[pos + 1] == '/') {
      pos += 2;
      while (pos < n && content[pos] != '\n') ++pos;
      continue;
    }
    if (c == '/' && pos + 1 < n && content[pos + 1] == '*') {
      pos += 2;
      while (pos + 1 < n && !(content[pos] == '*' && content[pos + 1] == '/')) {
        ++pos;
      }
      pos = (pos + 1 < n) ? pos + 2 : n;
      continue;
    }
    // A token is a maximal run of characters bounded by white space or a
    // comment.
    size_t begin = pos;
    while (pos < n) {
      char t = content[pos];
      if (is_space(t)) break;
      if (t == '/' && pos + 1 < n &&
          (content[pos + 1] == '/' || content[pos + 1] == '*')) {
        break;
      }
      ++pos;
    }
    std::string tok = content.substr(begin, pos - begin);
    if (tok.empty()) continue;

    if (tok[0] == '@') {
      // §21.4: an @-address is a hexadecimal index that repositions the load
      // cursor; no white space separates the '@' from its digits.
      int64_t addr =
          static_cast<int64_t>(std::strtoull(tok.c_str() + 1, nullptr, 16));
      if (!on_addr(addr)) return;
    } else {
      if (!on_word(tok)) return;
    }
  }
}

// §21.4: drives the address-windowed load shared by an ordinary unpacked array
// and by the §21.4.1 dynamic-array / queue forms. The window [low_addr,
// high_addr] is the set of addresses that may receive data; `store` deposits a
// parsed word at an address already known to lie within the window. The
// optional start_addr / finish_addr arguments fix the initial cursor, the load
// direction, and (with no file address) the expected word count.
template <class StoreFn>
static void EvalReadmemIndexed(const Expr* expr, SimContext& ctx, Arena& arena,
                               bool is_hex, const std::string& content,
                               int64_t low_addr, int64_t high_addr,
                               bool is_slice, uint32_t elem_width,
                               bool two_state, const EnumTypeInfo* enum_info,
                               StoreFn store) {
  bool has_start = expr->args.size() >= 3;
  bool has_finish = expr->args.size() >= 4;
  int64_t start_addr =
      has_start
          ? static_cast<int64_t>(EvalExpr(expr->args[2], ctx, arena).ToUint64())
          : low_addr;
  int64_t finish_addr =
      has_finish
          ? static_cast<int64_t>(EvalExpr(expr->args[3], ctx, arena).ToUint64())
          : high_addr;

  // §21.4: the direction of the highest dimension's entries follows the
  // relative magnitudes of start_addr and finish_addr. Loading runs downward
  // only when both bounds are supplied and start exceeds finish; otherwise it
  // runs upward. The chosen direction persists even past an @-address.
  bool descending = has_start && has_finish && start_addr > finish_addr;
  int64_t cursor = has_start ? start_addr : low_addr;

  // The address window the system-task arguments permit. When the task names a
  // start (and optionally a finish), addresses appearing in the file must lie
  // within this window.
  int64_t task_lo = has_finish ? std::min(start_addr, finish_addr) : start_addr;
  int64_t task_hi = has_finish ? std::max(start_addr, finish_addr) : high_addr;

  // §21.4: when slice syntax names the memory, the start_addr and finish_addr
  // arguments must fall within the slice's bounds.
  if (is_slice && has_start &&
      (start_addr < low_addr || start_addr > high_addr ||
       (has_finish && (finish_addr < low_addr || finish_addr > high_addr)))) {
    ctx.GetDiag().Error(
        {}, "$readmem" + std::string(is_hex ? "h" : "b") +
                ": start/finish address outside the slice bounds");
    return;
  }

  auto write_word = [&](int64_t addr, const Logic4Vec& v) {
    if (addr < low_addr || addr > high_addr) return;
    store(addr, v);
  };

  bool addr_in_file = false;
  bool aborted = false;
  uint64_t data_words = 0;
  ScanMemFile(
      content,
      [&](int64_t addr) -> bool {
        addr_in_file = true;
        if (has_start && (addr < task_lo || addr > task_hi)) {
          // §21.4: a file address outside the task-specified window is an error
          // and ends the load.
          ctx.GetDiag().Error(
              {}, "$readmem" + std::string(is_hex ? "h" : "b") +
                      ": file address outside the range given by the task");
          aborted = true;
          return false;
        }
        cursor = addr;
        return true;
      },
      [&](const std::string& tok) -> bool {
        Logic4Vec word = ParseMemNumber(arena, tok, is_hex, elem_width);
        // §21.4.2: a 2-state element retains no x/z; convert them to 0.
        if (two_state) CoerceToTwoState(word);
        // §21.4.2 (shall): a value outside the range of the enumerated element
        // type is an error, and no further data is read.
        if (enum_info && !EnumValueInRange(enum_info, word)) {
          ctx.GetDiag().Error(
              {}, "$readmem" + std::string(is_hex ? "h" : "b") +
                      ": value out of range for the enumerated type");
          aborted = true;
          return false;
        }
        write_word(cursor, word);
        ++data_words;
        cursor += descending ? -1 : 1;
        return true;
      });

  // §21.4: with an explicit start-through-finish window and no addresses in the
  // file, the data-word count must match the window size, else a warning is
  // issued. Addresses not covered by the file are left unmodified, which the
  // write loop above already guarantees.
  if (!aborted && has_start && has_finish && !addr_in_file) {
    uint64_t span = static_cast<uint64_t>(task_hi - task_lo + 1);
    if (data_words != span) {
      ctx.GetDiag().Warning(
          {}, "$readmem" + std::string(is_hex ? "h" : "b") +
                  ": number of data words differs from the address range");
    }
  }
}

// §21.4.1: loads an associative array. Each address — the start_addr default,
// the running cursor, or an @-address in the file — names an integral key, and
// depositing a word at a key creates the element when it does not already
// exist. The pattern file addresses elements numerically; when the index is an
// enumerated type, that number is the underlying numeric value of the
// enumeration element (see 6.19).
static void EvalReadmemAssoc(const Expr* expr, SimContext& ctx, Arena& arena,
                             bool is_hex, const std::string& content,
                             AssocArrayObject* aa, bool two_state,
                             const EnumTypeInfo* enum_info) {
  // §21.4.1: the index of an associative array loaded this way shall be of an
  // integral type. A string-keyed array has no numeric address form, so it
  // cannot be loaded.
  if (aa->is_string_key) {
    ctx.GetDiag().Error(
        {}, "$readmem" + std::string(is_hex ? "h" : "b") +
                ": associative array index must be of an integral type");
    return;
  }

  bool has_start = expr->args.size() >= 3;
  bool has_finish = expr->args.size() >= 4;
  int64_t start_addr =
      has_start
          ? static_cast<int64_t>(EvalExpr(expr->args[2], ctx, arena).ToUint64())
          : 0;
  int64_t finish_addr =
      has_finish
          ? static_cast<int64_t>(EvalExpr(expr->args[3], ctx, arena).ToUint64())
          : 0;
  bool descending = has_start && has_finish && start_addr > finish_addr;
  int64_t cursor = start_addr;

  ScanMemFile(
      content,
      [&](int64_t addr) -> bool {
        cursor = addr;
        return true;
      },
      [&](const std::string& tok) -> bool {
        Logic4Vec word = ParseMemNumber(arena, tok, is_hex, aa->elem_width);
        // §21.4.2: a 2-state element retains no x/z; convert them to 0.
        if (two_state) CoerceToTwoState(word);
        // §21.4.2 (shall): an out-of-range value for an enumerated element type
        // is an error that ends the load.
        if (enum_info && !EnumValueInRange(enum_info, word)) {
          ctx.GetDiag().Error(
              {}, "$readmem" + std::string(is_hex ? "h" : "b") +
                      ": value out of range for the enumerated type");
          return false;
        }
        // §21.4.1: loading an address creates its element if absent.
        aa->int_data[cursor] = word;
        cursor += descending ? -1 : 1;
        return true;
      });
}

// §21.4.3: loads a multidimensional unpacked array. The file is read in
// row-major order: the lowest (rightmost-declared) dimension varies the most
// rapidly, and each higher dimension's word entirely encloses the lower-
// dimension words beneath it. Every dimension's entries run from low to high
// address, so reversing the ascending/descending sense of a dimension's
// declaration does not change the file layout. An @-address in the file
// exclusively names a word of the highest (leftmost-declared) dimension and
// repositions the load to the first subword of that word. With or without
// addresses, when the file runs out of data the load stops and any array words
// or subwords not yet reached are left unchanged.
static void EvalReadmemMultiDim(const Expr* expr, SimContext& ctx, Arena& arena,
                                bool is_hex, const std::string& content,
                                const std::string& mem_name, const ArrayInfo* ai,
                                bool two_state,
                                const EnumTypeInfo* enum_info) {
  const std::vector<uint32_t>& los = ai->dim_los;
  const std::vector<uint32_t>& sizes = ai->dim_sizes;
  const size_t ndim = sizes.size();

  // §21.4.3: the number of subwords enclosed by a single highest-dimension word
  // is the product of every lower dimension's extent.
  uint64_t inner = 1;
  for (size_t d = 1; d < ndim; ++d) inner *= sizes[d];
  if (inner == 0) return;

  const int64_t top_lo = static_cast<int64_t>(los[0]);
  const int64_t top_hi = top_lo + static_cast<int64_t>(sizes[0]) - 1;

  // §21.4.3: a global position numbers every element of the array in row-major
  // order, so a sequential file fills element 0, 1, 2, ... regardless of how the
  // dimensions nest. The element name carries one bracketed subscript per
  // dimension (mem[i0][i1]...), each running from its dimension's low address.
  auto element_at = [&](uint64_t global) -> std::string {
    uint64_t top = global / inner;
    uint64_t flat = global % inner;
    std::string nm = mem_name + "[" + std::to_string(top_lo + static_cast<int64_t>(top)) + "]";
    // Decompose the within-word position into per-dimension subscripts,
    // innermost first (it varies fastest), then emit them outer-to-inner.
    std::vector<int64_t> subs(ndim - 1);
    for (size_t d = ndim - 1; d >= 1; --d) {
      subs[d - 1] = static_cast<int64_t>(los[d]) +
                    static_cast<int64_t>(flat % sizes[d]);
      flat /= sizes[d];
    }
    for (size_t d = 1; d < ndim; ++d) {
      nm += "[" + std::to_string(subs[d - 1]) + "]";
    }
    return nm;
  };

  const uint64_t total = static_cast<uint64_t>(sizes[0]) * inner;
  uint64_t cursor = 0;

  ScanMemFile(
      content,
      [&](int64_t addr) -> bool {
        // §21.4.3: an address entry names a highest-dimension word. Loading
        // resumes at the first subword enclosed by that word.
        if (addr < top_lo || addr > top_hi) {
          ctx.GetDiag().Error(
              {}, "$readmem" + std::string(is_hex ? "h" : "b") +
                      ": file address outside the highest dimension's range");
          return false;
        }
        cursor = static_cast<uint64_t>(addr - top_lo) * inner;
        return true;
      },
      [&](const std::string& tok) -> bool {
        if (cursor >= total) return false;  // array full; nothing more to fill
        Logic4Vec word = ParseMemNumber(arena, tok, is_hex, ai->elem_width);
        if (two_state) CoerceToTwoState(word);
        if (enum_info && !EnumValueInRange(enum_info, word)) {
          ctx.GetDiag().Error(
              {}, "$readmem" + std::string(is_hex ? "h" : "b") +
                      ": value out of range for the enumerated type");
          return false;
        }
        if (auto* var = ctx.FindVariable(element_at(cursor))) var->value = word;
        ++cursor;
        return true;
      });
}

// §21.4: $readmemb / $readmemh read a text file of white space, comments, and
// unsized numbers into the word elements of an unpacked array. §21.4.1 extends
// the same tasks to dynamic arrays and queues (whose size is fixed for the
// load) and to associative arrays (addressed by an integral key).
static Logic4Vec EvalReadmem(const Expr* expr, SimContext& ctx, Arena& arena,
                             bool is_hex) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 1, 0);
  // §21.4: the filename may be a string literal, a string-typed value, or an
  // integral value whose bytes spell the name; EvalStringArg covers all three.
  std::string filename = EvalStringArg(expr->args[0], ctx, arena);

  std::ifstream ifs(filename);
  if (!ifs.is_open()) {
    ctx.GetDiag().Warning(
        {}, "$readmem" + std::string(is_hex ? "h" : "b") +
                ": cannot open file: " + filename);
    return MakeLogic4VecVal(arena, 1, 0);
  }
  std::string content((std::istreambuf_iterator<char>(ifs)),
                      std::istreambuf_iterator<char>());

  // §21.4: memory_name is a bare unpacked array or a slice of one (the lowest
  // dimension may be written with slice syntax, see 7.4.5). The selected index
  // range is the address space the load works over.
  const Expr* mn = expr->args[1];
  const Expr* base_id = nullptr;
  bool is_slice = false;
  int64_t slice_lo = 0;
  int64_t slice_hi = 0;
  if (mn->kind == ExprKind::kIdentifier) {
    base_id = mn;
  } else if (mn->kind == ExprKind::kSelect && mn->index_end != nullptr &&
             !mn->is_part_select_plus && !mn->is_part_select_minus &&
             mn->base != nullptr && mn->base->kind == ExprKind::kIdentifier) {
    base_id = mn->base;
    is_slice = true;
    int64_t a = static_cast<int64_t>(EvalExpr(mn->index, ctx, arena).ToUint64());
    int64_t b =
        static_cast<int64_t>(EvalExpr(mn->index_end, ctx, arena).ToUint64());
    slice_lo = std::min(a, b);
    slice_hi = std::max(a, b);
  } else {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  std::string mem_name(base_id->text);

  // §21.4.2: when the memory's element type is enumerated, the file numbers are
  // the underlying numeric values of the type's elements and each must name a
  // valid element. A null result means the destination is not enum-typed.
  const EnumTypeInfo* enum_info = ctx.GetVariableEnumType(mem_name);

  // §21.4.1: an associative array is addressed by an integral key; addresses
  // create their elements on demand rather than indexing a fixed window.
  if (AssocArrayObject* aa = ctx.FindAssocArray(mem_name)) {
    EvalReadmemAssoc(expr, ctx, arena, is_hex, content, aa, !aa->is_4state,
                     enum_info);
    return MakeLogic4VecVal(arena, 1, 0);
  }

  // §21.4.1: a dynamic array or queue loads into its existing elements. The
  // current size is fixed for the load, so an address beyond the last element
  // is simply dropped — the array is never resized to make room.
  if (QueueObject* q = ctx.FindQueue(mem_name)) {
    int64_t low_addr = 0;
    int64_t high_addr = static_cast<int64_t>(q->elements.size()) - 1;
    if (is_slice) {
      low_addr = std::max(slice_lo, low_addr);
      high_addr = std::min(slice_hi, high_addr);
    }
    EvalReadmemIndexed(expr, ctx, arena, is_hex, content, low_addr, high_addr,
                       is_slice, q->elem_width, !q->is_4state, enum_info,
                       [&](int64_t addr, const Logic4Vec& v) {
                         q->elements[static_cast<size_t>(addr)] = v;
                       });
    return MakeLogic4VecVal(arena, 1, 0);
  }

  const ArrayInfo* ai = ctx.FindArrayInfo(mem_name);
  if (!ai) return MakeLogic4VecVal(arena, 1, 0);

  // §21.4.3: a memory with more than one unpacked dimension is filled in
  // row-major order, with @-addresses naming highest-dimension words. (A slice
  // memory_name resolves to a single lower dimension, see §7.4.5, and is handled
  // by the single-dimension path below.)
  if (!is_slice && ai->dim_sizes.size() >= 2) {
    EvalReadmemMultiDim(expr, ctx, arena, is_hex, content, mem_name, ai,
                        !ai->is_4state, enum_info);
    return MakeLogic4VecVal(arena, 1, 0);
  }

  int64_t arr_lo = ai->lo;
  int64_t arr_hi = ai->lo + static_cast<int64_t>(ai->size) - 1;
  // A slice narrows the load window to its own bounds (clamped to the array).
  int64_t low_addr = is_slice ? std::max(slice_lo, arr_lo) : arr_lo;
  int64_t high_addr = is_slice ? std::min(slice_hi, arr_hi) : arr_hi;

  EvalReadmemIndexed(expr, ctx, arena, is_hex, content, low_addr, high_addr,
                     is_slice, ai->elem_width, !ai->is_4state, enum_info,
                     [&](int64_t addr, const Logic4Vec& v) {
                       std::string elem =
                           mem_name + "[" + std::to_string(addr) + "]";
                       if (auto* var = ctx.FindVariable(elem)) var->value = v;
                     });
  return MakeLogic4VecVal(arena, 1, 0);
}

// §21.5: $writememb / $writememh dump a memory array's words to a file in a
// form the matching $readmemb / $readmemh can load back. Each word is written
// on its own line in binary ($writememb) or hexadecimal ($writememh).
// §21.5.3 fixes whether @-address specifiers accompany the words: an unpacked
// or dynamic array is written as a bare sequence (a sequential read reloads
// it), while an associative array prefixes every entry with its @-address.
static Logic4Vec EvalWritemem(const Expr* expr, SimContext& ctx, Arena& arena,
                              bool is_hex) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 1, 0);
  std::string filename = ExtractStrArg(expr->args[0]);

  if (expr->args[1]->kind != ExprKind::kIdentifier) {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  std::string mem_name(expr->args[1]->text);

  // §21.5: an existing file is overwritten; there is no append mode, so open
  // with truncation and discard any prior contents.
  std::ofstream ofs(filename, std::ios::out | std::ios::trunc);
  if (!ofs.is_open()) {
    std::cerr << "WARNING: $writemem" << (is_hex ? "h" : "b")
              << ": cannot open file: " << filename << "\n";
    return MakeLogic4VecVal(arena, 1, 0);
  }

  // Render one word in the radix the companion read task expects. FormatArg
  // carries arbitrary widths and preserves x/z bits, so the output stays
  // readable for vectors wider than a machine word.
  auto emit = [&](const Logic4Vec& v) {
    ofs << FormatArg(v, is_hex ? 'h' : 'b') << "\n";
  };

  // §21.5.3: an associative array's keys are sparse, so a plain sequential read
  // could not place its words. Each entry is therefore written with an
  // @-address ahead of its value. The keys are integral (§21.4.1) and emitted
  // in ascending order as hexadecimal, matching the @-address form $readmem
  // parses.
  if (const AssocArrayObject* aa = ctx.FindAssocArray(mem_name)) {
    for (const auto& entry : aa->int_data) {
      char addr_buf[20];
      std::snprintf(addr_buf, sizeof(addr_buf), "%llx",
                    static_cast<unsigned long long>(entry.first));
      ofs << "@" << addr_buf << "\n";
      emit(entry.second);
    }
    return MakeLogic4VecVal(arena, 1, 0);
  }

  // §21.5.3: a dynamic array or queue is written as a bare sequence of words
  // with no @-address specifiers, exactly like a fixed unpacked array, so a
  // sequential $readmem reloads it. The optional start_addr / finish_addr
  // bound the element indices that are written.
  if (const QueueObject* q = ctx.FindQueue(mem_name)) {
    int64_t arr_lo = 0;
    int64_t arr_hi = static_cast<int64_t>(q->elements.size()) - 1;
    bool has_start = expr->args.size() >= 3;
    bool has_finish = expr->args.size() >= 4;
    int64_t start_addr =
        has_start
            ? static_cast<int64_t>(EvalExpr(expr->args[2], ctx, arena).ToUint64())
            : arr_lo;
    int64_t finish_addr =
        has_finish
            ? static_cast<int64_t>(EvalExpr(expr->args[3], ctx, arena).ToUint64())
            : arr_hi;
    if (arr_hi < arr_lo) return MakeLogic4VecVal(arena, 1, 0);
    int64_t step = (start_addr <= finish_addr) ? 1 : -1;
    for (int64_t addr = start_addr;; addr += step) {
      if (addr >= arr_lo && addr <= arr_hi) {
        emit(q->elements[static_cast<size_t>(addr)]);
      }
      if (addr == finish_addr) break;
    }
    return MakeLogic4VecVal(arena, 1, 0);
  }

  if (const ArrayInfo* ai = ctx.FindArrayInfo(mem_name)) {
    int64_t arr_lo = ai->lo;
    int64_t arr_hi = ai->lo + static_cast<int64_t>(ai->size) - 1;
    // The optional start_addr / finish_addr bound the range that is written;
    // a finish below start emits the words in descending address order.
    bool has_start = expr->args.size() >= 3;
    bool has_finish = expr->args.size() >= 4;
    int64_t start_addr =
        has_start
            ? static_cast<int64_t>(EvalExpr(expr->args[2], ctx, arena).ToUint64())
            : arr_lo;
    int64_t finish_addr =
        has_finish
            ? static_cast<int64_t>(EvalExpr(expr->args[3], ctx, arena).ToUint64())
            : arr_hi;
    int64_t step = (start_addr <= finish_addr) ? 1 : -1;
    for (int64_t addr = start_addr;; addr += step) {
      if (addr >= arr_lo && addr <= arr_hi) {
        std::string elem = mem_name + "[" + std::to_string(addr) + "]";
        if (auto* var = ctx.FindVariable(elem)) emit(var->value);
      }
      if (addr == finish_addr) break;
    }
    return MakeLogic4VecVal(arena, 1, 0);
  }

  // A plain variable names a single memory word.
  if (auto* target = ctx.FindVariable(mem_name)) emit(target->value);
  return MakeLogic4VecVal(arena, 1, 0);
}

// §21.3.4.3: integer conversion codes are case-insensitive (%d or %D, etc.).
// Returns the numeric base, or 0 for a code not treated as an integer field.
static int SpecToBase(char spec) {
  char c = (spec >= 'A' && spec <= 'Z') ? static_cast<char>(spec - 'A' + 'a')
                                        : spec;
  if (c == 'd') return 10;
  if (c == 'h' || c == 'x') return 16;
  if (c == 'b') return 2;
  if (c == 'o') return 8;
  return 0;
}

// §21.3.4.3: leading white space ahead of an input field is ignored. This is
// the same set $fscanf recognizes (blanks, tabs, newlines, formfeeds, and the
// related vertical tab and carriage return).
static bool IsScanSpace(char c) {
  return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' ||
         c == '\v';
}

static std::string EvalStringArg(const Expr* arg, SimContext& ctx,
                                 Arena& arena) {
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
static std::string ResolveFormatArg(const Expr* arg, SimContext& ctx,
                                    Arena& arena) {
  if (arg && arg->kind == ExprKind::kStringLiteral) {
    return ExtractFormatString(arg);
  }
  return EvalStringArg(arg, ctx, arena);
}

// §21.3.4.3: a four-state value with any unknown bit (x or z) cannot be read as
// ASCII text. Only a non-literal argument can carry such bits.
static bool ScanArgHasUnknownBits(const Expr* arg, SimContext& ctx,
                                  Arena& arena) {
  if (!arg || arg->kind == ExprKind::kStringLiteral) return false;
  Logic4Vec v = EvalExpr(arg, ctx, arena);
  for (uint32_t w = 0; w < v.nwords; ++w) {
    if (v.words[w].bval != 0) return true;
  }
  return false;
}

// §21.3.4.3: pack a matched string/character field into a destination, placing
// the leftmost character in the most significant byte.
static Logic4Vec ScanStringToVec(Arena& arena, const std::string& str,
                                 uint32_t width) {
  auto vec = MakeLogic4VecVal(arena, width, 0);
  for (size_t i = 0; i < str.size() && i * 8 < width; ++i) {
    auto byte_idx = static_cast<uint32_t>(str.size() - 1 - i);
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    if (word < vec.nwords) {
      vec.words[word].aval |= static_cast<uint64_t>(static_cast<uint8_t>(str[i]))
                              << bit;
    }
  }
  return vec;
}

// §21.3.4.3: store a converted real value (its IEEE-754 bit pattern) into a
// real destination.
static void StoreRealField(Variable* var, Arena& arena, double d) {
  if (!var) return;
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  uint32_t width = var->value.width ? var->value.width : 64;
  auto vec = MakeLogic4VecVal(arena, width, bits);
  vec.is_real = true;
  var->value = vec;
}

// §21.3.4.3 scan engine shared in spirit with $fscanf. Interprets `fmt` against
// `input`, assigning converted fields to the destination arguments; returns the
// count of assigned items and reports the consumed input length.
static uint32_t RunScanf(const std::string& input, const std::string& fmt,
                         Expr* const* dest, size_t ndest, SimContext& ctx,
                         Arena& arena, size_t& consumed) {
  size_t pos = 0;
  size_t ai = 0;
  uint32_t matched = 0;

  auto field_var = [&](bool suppress) -> Variable* {
    if (suppress || ai >= ndest) return nullptr;
    const Expr* a = dest[ai];
    if (a->kind == ExprKind::kIdentifier) return ctx.FindVariable(a->text);
    return nullptr;
  };
  auto upper_limit = [&](int width) -> size_t {
    if (width > 0 && pos + static_cast<size_t>(width) < input.size())
      return pos + static_cast<size_t>(width);
    return input.size();
  };

  for (size_t fi = 0; fi < fmt.size(); ++fi) {
    char fc = fmt[fi];

    // §21.3.4.3 (a): white space in the control string skips a run of input
    // white space.
    if (IsScanSpace(fc)) {
      while (pos < input.size() && IsScanSpace(input[pos])) ++pos;
      continue;
    }

    // §21.3.4.3 (b): an ordinary character must match the next input character.
    if (fc != '%') {
      if (pos >= input.size() || input[pos] != fc) break;
      ++pos;
      continue;
    }

    if (fi + 1 >= fmt.size()) break;
    ++fi;
    // §21.3.4.3 (c): optional assignment-suppression character.
    bool suppress = false;
    if (fmt[fi] == '*') {
      suppress = true;
      if (++fi >= fmt.size()) break;
    }
    // §21.3.4.3 (c): optional maximum field width.
    int width = 0;
    while (fi < fmt.size() && fmt[fi] >= '0' && fmt[fi] <= '9') {
      width = width * 10 + (fmt[fi] - '0');
      ++fi;
    }
    if (fi >= fmt.size()) break;
    char code = fmt[fi];
    char lc = (code >= 'A' && code <= 'Z') ? static_cast<char>(code - 'A' + 'a')
                                           : code;

    if (lc == '%') {
      if (pos >= input.size() || input[pos] != '%') break;
      ++pos;
      continue;
    }

    if (lc == 'c') {
      // §21.3.4.3: the character conversion does not skip leading white space.
      int cnt = width > 0 ? width : 1;
      if (pos >= input.size()) break;
      std::string chars;
      for (int k = 0; k < cnt && pos < input.size(); ++k) chars += input[pos++];
      Variable* var = field_var(suppress);
      if (var) {
        if (chars.size() == 1) {
          var->value = MakeLogic4VecVal(arena, var->value.width,
                                        static_cast<uint8_t>(chars[0]));
        } else {
          var->value = ScanStringToVec(arena, chars, var->value.width);
        }
      }
      if (!suppress) {
        ++matched;
        ++ai;
      }
      continue;
    }

    // §21.3.4.3: every remaining conversion ignores leading white space.
    while (pos < input.size() && IsScanSpace(input[pos])) ++pos;

    if (lc == 's') {
      size_t limit = upper_limit(width);
      std::string s;
      while (pos < limit && !IsScanSpace(input[pos])) s += input[pos++];
      if (s.empty()) break;
      Variable* var = field_var(suppress);
      if (var) var->value = ScanStringToVec(arena, s, var->value.width);
      if (!suppress) {
        ++matched;
        ++ai;
      }
      continue;
    }

    if (lc == 'f' || lc == 'e' || lc == 'g' || lc == 't') {
      size_t limit = upper_limit(width);
      std::string sub = input.substr(pos, limit - pos);
      const char* c = sub.c_str();
      char* end = nullptr;
      double d = std::strtod(c, &end);
      if (end == c) break;
      pos += static_cast<size_t>(end - c);
      StoreRealField(field_var(suppress), arena, d);
      if (!suppress) {
        ++matched;
        ++ai;
      }
      continue;
    }

    if (lc == 'u') {
      // §21.3.4.3, Table 21-7: %u transfers unformatted 2-value binary data,
      // pulling enough raw bytes to fill the destination in the host's native
      // (little-endian) byte order. The bytes are known, so the stored value
      // carries no x or z.
      Variable* var = field_var(suppress);
      uint32_t w = var ? var->value.width : 8;
      size_t nbytes = (w + 7) / 8;
      if (pos + nbytes > input.size()) break;  // too little data to fill target
      uint64_t v = 0;
      for (size_t k = 0; k < nbytes && k < sizeof(uint64_t); ++k) {
        v |= static_cast<uint64_t>(static_cast<uint8_t>(input[pos + k]))
             << (8 * k);
      }
      pos += nbytes;
      if (var) var->value = MakeLogic4VecVal(arena, var->value.width, v);
      if (!suppress) {
        ++matched;
        ++ai;
      }
      continue;
    }

    int base = SpecToBase(lc);
    if (base == 0) break;  // unsupported conversion code: stop scanning
    size_t limit = upper_limit(width);
    std::string sub = input.substr(pos, limit - pos);
    const char* c = sub.c_str();
    char* end = nullptr;
    unsigned long long v = std::strtoull(c, &end, base);
    if (end == c) break;
    pos += static_cast<size_t>(end - c);
    Variable* var = field_var(suppress);
    if (var) {
      var->value =
          MakeLogic4VecVal(arena, var->value.width, static_cast<uint64_t>(v));
    }
    if (!suppress) {
      ++matched;
      ++ai;
    }
  }

  consumed = pos;
  return matched;
}

static Logic4Vec EvalSscanf(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 3) return MakeLogic4VecVal(arena, 32, 0);

  // §21.3.4.3: when the str argument or the format string carries an unknown
  // bit (x or z), $sscanf reports EOF (-1).
  if (ScanArgHasUnknownBits(expr->args[0], ctx, arena) ||
      ScanArgHasUnknownBits(expr->args[1], ctx, arena)) {
    return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);
  }

  std::string input = EvalStringArg(expr->args[0], ctx, arena);
  std::string fmt = ExtractStrArg(expr->args[1]);

  size_t consumed = 0;
  uint32_t matched = RunScanf(input, fmt, expr->args.data() + 2,
                              expr->args.size() - 2, ctx, arena, consumed);

  // §21.3.4.3: zero signals a matching failure against present input, while EOF
  // (-1) is returned when the input is exhausted before any field converts.
  if (matched == 0) {
    size_t p = consumed;
    while (p < input.size() && IsScanSpace(input[p])) ++p;
    if (p >= input.size()) return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);
  }
  return MakeLogic4VecVal(arena, 32, matched);
}

// ---------------------------------------------------------------------------
// §20.16 / §20.16.1: programmable logic array (PLA) modeling system tasks.
// ---------------------------------------------------------------------------

namespace {

// §20.16, Table 20-12: a PLA task is named $<array_type>$<logic>$<format>. These
// are the decoded components that drive evaluation.
struct PlaTaskKind {
  bool valid = false;
  bool is_async = false;  // §20.16.1: asynchronous vs synchronous array
  enum class Logic { kAnd, kOr, kNand, kNor } logic = Logic::kAnd;
  bool is_plane = false;  // §20.16.4 format: array vs plane
};

// §20.16: split a callee into its three dollar-separated components and decide
// whether it names one of the sixteen tasks of Table 20-12. This mirrors the
// elaborator's IsPlaSystemTask recognizer but also keeps the decoded fields.
PlaTaskKind ClassifyPlaTask(std::string_view callee) {
  PlaTaskKind k;
  if (callee.empty() || callee.front() != '$') return k;
  std::string_view rest = callee.substr(1);
  auto take = [&rest]() -> std::string_view {
    auto pos = rest.find('$');
    std::string_view tok = rest.substr(0, pos);
    rest = pos == std::string_view::npos ? std::string_view{}
                                         : rest.substr(pos + 1);
    return tok;
  };
  std::string_view type = take();
  std::string_view logic = take();
  std::string_view format = take();
  if (!rest.empty()) return k;  // more than three components
  if (type == "sync") {
    k.is_async = false;
  } else if (type == "async") {
    k.is_async = true;
  } else {
    return k;
  }
  if (logic == "and") {
    k.logic = PlaTaskKind::Logic::kAnd;
  } else if (logic == "or") {
    k.logic = PlaTaskKind::Logic::kOr;
  } else if (logic == "nand") {
    k.logic = PlaTaskKind::Logic::kNand;
  } else if (logic == "nor") {
    k.logic = PlaTaskKind::Logic::kNor;
  } else {
    return k;
  }
  if (format == "array") {
    k.is_plane = false;
  } else if (format == "plane") {
    k.is_plane = true;
  } else {
    return k;
  }
  k.valid = true;
  return k;
}

// A single 4-state bit at position `p` of `v`, packed into bit position 0.
Logic4Word PlaBitAt(const Logic4Vec& v, uint32_t p) {
  if (p >= v.width) return {0, 0};
  uint32_t w = p / 64, b = p % 64;
  return {(v.words[w].aval >> b) & 1ULL, (v.words[w].bval >> b) & 1ULL};
}

void PlaSetBit(Logic4Vec& v, uint32_t pos, Logic4Word bit) {
  if (pos >= v.width) return;
  uint32_t w = pos / 64, b = pos % 64;
  v.words[w].aval |= (bit.aval & 1ULL) << b;
  v.words[w].bval |= (bit.bval & 1ULL) << b;
}

// §20.16.1: reduce the input terms selected by one personality word into a
// single output-term bit. The logic component fixes whether the participating
// inputs are AND- or OR-reduced, and the complemented forms (nand/nor) invert
// the result.
//
// §20.16.4 defines two personality formats, chosen by the format component of
// the task name (array vs plane). In the array format a personality bit of 1
// takes the input value and any other bit does not take it. In the plane
// (Berkeley Espresso) format the bit instead selects how the input
// participates: 0 takes the complemented input, 1 takes the true input, a
// don't-care (z, and the equivalent ?) drops the input from the reduction, and
// x takes the worst case by contributing an unknown. In the 4-state encoding a
// personality bit holds 0 as {0,0}, 1 as {1,0}, x as {1,1} and z/? as {0,1}.
Logic4Word PlaReduceWord(const PlaTaskKind& k, const Logic4Vec& mem_word,
                         const Logic4Vec& inputs, uint32_t n) {
  bool is_and = k.logic == PlaTaskKind::Logic::kAnd ||
                k.logic == PlaTaskKind::Logic::kNand;
  Logic4Word acc = is_and ? Logic4Word{1, 0} : Logic4Word{0, 0};
  for (uint32_t p = 0; p < n; ++p) {
    Logic4Word code = PlaBitAt(mem_word, p);
    Logic4Word in_bit = PlaBitAt(inputs, p);
    Logic4Word term;
    bool participates = true;
    if (k.is_plane) {
      // §20.16.4 plane-format (Espresso) personality codes.
      if (code.bval == 0) {
        // 1 takes the true input value, 0 takes the complemented input value.
        term = code.aval == 1 ? in_bit : Logic4Not(in_bit);
      } else if (code.aval == 1) {
        // x: take the worst case of the input value - contribute an unknown.
        term = Logic4Word{0, 1};
      } else {
        // z (and the equivalent ?): do-not-care, the input does not participate.
        participates = false;
      }
    } else {
      // §20.16.4 array-format personality codes: 1 takes the input value.
      participates = code.aval == 1 && code.bval == 0;
      term = in_bit;
    }
    if (participates) {
      acc = is_and ? Logic4And(acc, term) : Logic4Or(acc, term);
    }
  }
  bool invert = k.logic == PlaTaskKind::Logic::kNand ||
                k.logic == PlaTaskKind::Logic::kNor;
  return invert ? Logic4Not(acc) : acc;
}

// §20.16.1: perform one evaluation of the array from its current personality
// memory and input terms and drive the output terms with no delay. Silently
// does nothing when the call is malformed or the personality memory is unknown.
void EvaluatePla(const Expr* call, const PlaTaskKind& k, SimContext& ctx,
                 Arena& arena) {
  if (call->args.size() < 3 || !call->args[0] || !call->args[1] ||
      !call->args[2])
    return;
  if (call->args[0]->kind != ExprKind::kIdentifier) return;
  const ArrayInfo* ai = ctx.FindArrayInfo(call->args[0]->text);
  if (!ai || ai->size == 0) return;
  uint32_t n = ai->elem_width;  // §20.16.3: word width == number of input terms
  uint32_t m = ai->size;        // depth == number of output terms
  Logic4Vec inputs = EvalExpr(call->args[1], ctx, arena);
  Logic4Vec result = MakeLogic4Vec(arena, m);
  std::string mem_name(call->args[0]->text);
  for (uint32_t j = 0; j < m; ++j) {
    std::string elem = mem_name + "[" + std::to_string(ai->lo + j) + "]";
    Variable* word_var = ctx.FindVariable(elem);
    Logic4Vec word = word_var ? word_var->value : MakeLogic4Vec(arena, n);
    Logic4Word out_bit = PlaReduceWord(k, word, inputs, n);
    // §20.16.3: terms and memory are specified in ascending order, so the
    // lowest memory address corresponds to the most significant output term.
    PlaSetBit(result, m - 1 - j, out_bit);
  }
  // §20.16.1: "the output terms are updated without any delay" - an immediate
  // (blocking) write into the output-terms lvalue.
  PerformBlockingAssign(call->args[2], result, ctx, arena);
}

// Gathers the simple signal names referenced anywhere in the input-terms
// argument, so the asynchronous forms can watch each one for changes.
void CollectPlaInputSignals(const Expr* e,
                            std::vector<std::string_view>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kIdentifier) {
    out.push_back(e->text);
    return;
  }
  CollectPlaInputSignals(e->lhs, out);
  CollectPlaInputSignals(e->rhs, out);
  CollectPlaInputSignals(e->base, out);
  CollectPlaInputSignals(e->index, out);
  CollectPlaInputSignals(e->index_end, out);
  for (auto* a : e->args) CollectPlaInputSignals(a, out);
  for (auto* el : e->elements) CollectPlaInputSignals(el, out);
}

}  // namespace

bool TryEvalPlaSystemTask(const Expr* expr, SimContext& ctx, Arena& arena) {
  PlaTaskKind k = ClassifyPlaTask(expr->callee);
  if (!k.valid) return false;
  // §20.16.1: both array types evaluate immediately when the task is called and
  // update the outputs without delay. For the synchronous forms this single
  // evaluation is the whole behavior - the call site controls the time at which
  // the array is evaluated and the outputs updated.
  EvaluatePla(expr, k, ctx, arena);
  if (k.is_async) {
    // §20.16.1: the asynchronous forms additionally re-evaluate on their own
    // whenever an input term changes value or any word of the personality
    // memory is changed. Install a persistent watcher on each input signal and
    // each memory word that recomputes and re-drives the outputs.
    auto reeval = [expr, k, &ctx, &arena]() -> bool {
      EvaluatePla(expr, k, ctx, arena);
      return false;  // keep watching
    };
    std::vector<std::string_view> names;
    if (expr->args.size() >= 2) CollectPlaInputSignals(expr->args[1], names);
    for (auto name : names) {
      if (Variable* v = ctx.FindVariable(name)) v->AddWatcher(reeval);
    }
    if (!expr->args.empty() && expr->args[0] &&
        expr->args[0]->kind == ExprKind::kIdentifier) {
      if (const ArrayInfo* ai = ctx.FindArrayInfo(expr->args[0]->text)) {
        std::string mem_name(expr->args[0]->text);
        for (uint32_t j = 0; j < ai->size; ++j) {
          std::string elem = mem_name + "[" + std::to_string(ai->lo + j) + "]";
          if (Variable* v = ctx.FindVariable(elem)) v->AddWatcher(reeval);
        }
      }
    }
  }
  return true;
}

Logic4Vec EvalIOSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                        std::string_view name) {
  if (name == "$fopen") return EvalFopen(expr, ctx, arena);
  if (name == "$fclose") return EvalFclose(expr, ctx, arena);
  if (IsFileOutputTask(name)) {
    return EvalFdisplayWrite(expr, ctx, arena, name);
  }
  if (name == "$readmemh") return EvalReadmem(expr, ctx, arena, true);
  if (name == "$readmemb") return EvalReadmem(expr, ctx, arena, false);
  if (name == "$writememh") return EvalWritemem(expr, ctx, arena, true);
  if (name == "$writememb") return EvalWritemem(expr, ctx, arena, false);
  if (name == "$sscanf") return EvalSscanf(expr, ctx, arena);
  // §21.3.3: the $swrite family and $sformat target a variable rather than a
  // file descriptor but otherwise mirror their $fwrite / $fdisplay
  // counterparts.
  if (name == "$swrite" || name == "$swriteb" || name == "$swriteh" ||
      name == "$swriteo") {
    return EvalSwriteFamily(expr, ctx, arena, name);
  }
  if (name == "$sformat") return EvalSformatTask(expr, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

}
