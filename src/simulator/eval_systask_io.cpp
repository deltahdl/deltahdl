#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "parser/ast.h"
#include "simulator/eval_string.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

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
      out += FormatDisplay(fmt, vals, {.ctx = &ctx});
      continue;
    }
    auto val = EvalExpr(a, ctx, arena);
    char spec = val.is_string ? 's' : default_radix;
    char fmt_buf[3] = {'%', spec, 0};
    out += FormatDisplay(fmt_buf, {val}, {.ctx = &ctx});
  }
  return out;
}

// §21.3.3 N7 (and §5.9): store the formatted output into the destination
// variable using the string-literal assignment-to-variable rules. A
// `string`-typed destination is variable-width and holds exactly the packed
// characters (leading NULs dropped, as any string assignment does). A
// fixed-width integral destination is coerced to its declared width: the
// leftmost character lands in the highest byte (left-bound to right-bound
// ordering), so a wider destination is zero-padded on the left (right-
// justified) and a narrower one is truncated from the left, discarding the
// earliest characters. Previously the write ignored the destination width and
// silently redefined it to the string length, violating §5.9 for fixed-width
// targets.
static void StoreStringResult(Variable* dst, std::string_view name,
                              const std::string& output, SimContext& ctx,
                              Arena& arena) {
  if (dst != nullptr) {
    Logic4Vec packed = StringToLogic4Vec(arena, output);
    if (ctx.IsStringVariable(name)) {
      dst->value = StripStringZeros(packed, arena);
    } else {
      dst->value = ResizeToWidth(packed, dst->value.width, arena);
    }
    return;
  }
  // §21.3.3: the destination may instead be an unpacked array of byte, which is
  // lowered to one element variable per index rather than a single variable, so
  // FindVariable does not resolve it. Distribute the formatted characters
  // across the elements from the array's left bound to its right bound -- the
  // leftmost character lands in the left-bound element. Elements beyond the end
  // of the string are cleared, and characters beyond the end of the array are
  // dropped.
  const ArrayInfo* ai = ctx.FindArrayInfo(name);
  if (ai == nullptr || ai->is_dynamic || ai->is_queue ||
      ai->elem_type_kind != DataTypeKind::kByte) {
    return;
  }
  for (uint32_t i = 0; i < ai->size; ++i) {
    uint32_t idx =
        ai->is_descending ? (ai->lo + ai->size - 1 - i) : (ai->lo + i);
    std::string ename = std::string(name) + "[" + std::to_string(idx) + "]";
    Variable* elem = ctx.FindVariable(ename);
    if (elem == nullptr) continue;
    uint8_t byte = i < output.size() ? static_cast<uint8_t>(output[i]) : 0;
    elem->value = MakeLogic4VecVal(arena, ai->elem_width, byte);
  }
}

// §21.3.3 N6: $swrite/$swriteb/$swriteh/$swriteo take an output variable as
// the first argument and write the formatted result into it under string-
// literal assignment-to-variable rules. The b/h/o suffix selects the default
// radix for bare expression arguments per §21.3.2.
static Logic4Vec EvalSwriteFamily(const Expr* expr, SimContext& ctx,
                                  Arena& arena, std::string_view name) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  Variable* dst = nullptr;
  std::string_view dst_name;
  if (expr->args[0] && expr->args[0]->kind == ExprKind::kIdentifier) {
    dst_name = expr->args[0]->text;
    dst = ctx.FindVariable(dst_name);
  }

  // The suffix character ('\0' / b / h / o) becomes the default radix letter
  // for bare expression arguments. Without a suffix, decimal is the default.
  char default_radix = 'd';
  if (name.size() >= 1) {
    char back = name.back();
    if (back == 'b' || back == 'h' || back == 'o') default_radix = back;
  }

  std::vector<Expr*> rest(expr->args.begin() + 1, expr->args.end());
  std::string output = BuildStringTaskOutput(rest, default_radix, ctx, arena);
  StoreStringResult(dst, dst_name, output, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

// §21.3.3 N9: $sformat always interprets its second argument, and only its
// second argument, as the format string; following arguments fill its
// specifiers in order and are never re-interpreted as format strings.
static Logic4Vec EvalSformatTask(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 1, 0);
  Variable* dst = nullptr;
  std::string_view dst_name;
  if (expr->args[0] && expr->args[0]->kind == ExprKind::kIdentifier) {
    dst_name = expr->args[0]->text;
    dst = ctx.FindVariable(dst_name);
  }
  std::string fmt = ResolveFormatArg(expr->args[1], ctx, arena);
  std::vector<Logic4Vec> vals;
  for (size_t i = 2; i < expr->args.size(); ++i) {
    vals.push_back(EvalExpr(expr->args[i], ctx, arena));
  }
  WarnIfArgCountMismatch(ctx, "$sformat", fmt, vals.size());
  std::string out = FormatDisplay(fmt, vals, {.ctx = &ctx});
  StoreStringResult(dst, dst_name, out, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

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
  bool is_display_family = name.rfind("$fdisplay", 0) == 0 ||
                           name.rfind("$fstrobe", 0) == 0 ||
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
    output = FormatDisplay(fmt, arg_vals, {.ctx = &ctx});
  } else if (suffix != '\0') {
    // §21.3.2 derives b/h/o radix from the task-name suffix when no format
    // string is supplied.
    char fmt_buf[3] = {'%', suffix, 0};
    output = FormatDisplay(fmt_buf, arg_vals, {.ctx = &ctx});
  }
  for (FILE* fp : targets) {
    // Written by size, not as a C string: the unformatted %u / %z renderings
    // (§21.2.1.1) legitimately contain NUL bytes, which must reach the file
    // intact for a §21.3.4.3 $fscanf round trip to recover the value.
    std::fwrite(output.data(), 1, output.size(), fp);
    if (is_display_family) std::fputc('\n', fp);
    std::fflush(fp);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

// §21.3.4.3: integer conversion codes are case-insensitive (%d or %D, etc.).
// Returns the numeric base, or 0 for a code not treated as an integer field.
static int SpecToBase(char spec) {
  char c =
      (spec >= 'A' && spec <= 'Z') ? static_cast<char>(spec - 'A' + 'a') : spec;
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

// §21.3.4.3: a four-state value with any unknown bit (x or z) cannot be read as
// ASCII text. Only a non-literal argument can carry such bits. An unpacked
// byte array is lowered to per-element variables, so it is decoded per element
// rather than evaluated as one packed value.
static bool ScanArgHasUnknownBits(const Expr* arg, SimContext& ctx,
                                  Arena& arena) {
  if (!arg || arg->kind == ExprKind::kStringLiteral) return false;
  if (arg->kind == ExprKind::kIdentifier &&
      ctx.FindArrayInfo(arg->text) != nullptr) {
    return false;
  }
  Logic4Vec v = EvalExpr(arg, ctx, arena);
  for (uint32_t w = 0; w < v.nwords; ++w) {
    if (v.words[w].bval != 0) return true;
  }
  return false;
}

// §21.3.4.3: pack a matched string/character field into a destination, placing
// the leftmost character in the most significant byte.
Logic4Vec ScanStringToVec(Arena& arena, const std::string& str,
                          uint32_t width) {
  auto vec = MakeLogic4VecVal(arena, width, 0);
  for (size_t i = 0; i < str.size() && i * 8 < width; ++i) {
    auto byte_idx = static_cast<uint32_t>(str.size() - 1 - i);
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    if (word < vec.nwords) {
      vec.words[word].aval |=
          static_cast<uint64_t>(static_cast<uint8_t>(str[i])) << bit;
    }
  }
  return vec;
}

// §21.3.4.3: store a converted real value (its IEEE-754 bit pattern) into a
// real destination.
void StoreRealField(Variable* var, Arena& arena, double d) {
  if (!var) return;
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  uint32_t width = var->value.width ? var->value.width : 64;
  auto vec = MakeLogic4VecVal(arena, width, bits);
  vec.is_real = true;
  var->value = vec;
}

// Outcome of handling one §21.3.4.3 conversion specifier. `kStop` ends the
// scan with no further bookkeeping; `kMatched` means a field converted (the
// caller advances the match/arg counters unless the field was suppressed);
// `kSkipped` means the specifier consumed input but produces no assigned field
// (the %% literal match), so the caller only continues.
enum class ScanFieldResult : std::uint8_t { kStop, kMatched, kSkipped };

// State carried across the per-specifier handlers. `pos` is the current read
// offset into the input; the helpers advance it in place.
namespace {
struct ScanCursor {
  const std::string& input;
  size_t& pos;
};

// §21.3.4.3 (c) maximum-field-width clamp: the field ends at `pos+width` when a
// positive width still leaves room inside the input, otherwise at end of input.
size_t ScanUpperLimit(const ScanCursor& cur, int width) {
  if (width > 0 && cur.pos + static_cast<size_t>(width) < cur.input.size())
    return cur.pos + static_cast<size_t>(width);
  return cur.input.size();
}

// The destination of one conversion. Beyond the plain variable, §21.3.4.3
// admits a string-typed destination (variable-width, holds exactly the matched
// characters) and, for %s, an unpacked array of byte whose elements each take
// one character. `name` backs the per-element writes of the byte-array form.
struct ScanDest {
  Variable* var = nullptr;
  bool is_string = false;
  const ArrayInfo* byte_array = nullptr;
  std::string_view name;
};

// §21.3.4.3: store a matched character run into the destination. A string
// destination resizes to the exact run; a packed destination takes the
// leftmost character in its most significant byte; an unpacked byte array
// takes one character per element from its left bound, clearing elements
// beyond the run and dropping characters beyond the array.
void StoreScannedChars(const ScanDest& dst, const std::string& s,
                       SimContext& ctx, Arena& arena) {
  if (dst.byte_array != nullptr) {
    const ArrayInfo* ai = dst.byte_array;
    for (uint32_t i = 0; i < ai->size; ++i) {
      uint32_t idx =
          ai->is_descending ? (ai->lo + ai->size - 1 - i) : (ai->lo + i);
      std::string ename =
          std::string(dst.name) + "[" + std::to_string(idx) + "]";
      Variable* elem = ctx.FindVariable(ename);
      if (elem == nullptr) continue;
      uint8_t byte = i < s.size() ? static_cast<uint8_t>(s[i]) : 0;
      elem->value = MakeLogic4VecVal(arena, ai->elem_width, byte);
    }
    return;
  }
  if (dst.var == nullptr) return;
  if (dst.is_string) {
    dst.var->value =
        ScanStringToVec(arena, s, static_cast<uint32_t>(s.size()) * 8);
  } else {
    dst.var->value = ScanStringToVec(arena, s, dst.var->value.width);
  }
}

// §21.3.4.3: the character conversion does not skip leading white space; it
// copies `width` (default 1) raw characters into the destination.
ScanFieldResult ScanCharField(ScanCursor cur, int width, const ScanDest& dst,
                              SimContext& ctx, Arena& arena) {
  int cnt = width > 0 ? width : 1;
  if (cur.pos >= cur.input.size()) return ScanFieldResult::kStop;
  std::string chars;
  for (int k = 0; k < cnt && cur.pos < cur.input.size(); ++k)
    chars += cur.input[cur.pos++];
  if (chars.size() == 1 && dst.var && !dst.is_string) {
    dst.var->value = MakeLogic4VecVal(arena, dst.var->value.width,
                                      static_cast<uint8_t>(chars[0]));
  } else {
    StoreScannedChars(dst, chars, ctx, arena);
  }
  return ScanFieldResult::kMatched;
}

// §21.3.4.3: %s gathers a run of non-white-space characters (bounded by the
// field width) into the destination.
ScanFieldResult ScanStringField(ScanCursor cur, int width, const ScanDest& dst,
                                SimContext& ctx, Arena& arena) {
  size_t limit = ScanUpperLimit(cur, width);
  std::string s;
  while (cur.pos < limit && !IsScanSpace(cur.input[cur.pos]))
    s += cur.input[cur.pos++];
  if (s.empty()) return ScanFieldResult::kStop;
  StoreScannedChars(dst, s, ctx, arena);
  return ScanFieldResult::kMatched;
}

// §21.3.4.3, Table 21-7: %t matches a floating-point number that is then
// scaled and rounded according to the $timeformat configuration (§20.4.3):
// the matched value is in $timeformat units, rounded to the configured number
// of fractional digits, and expressed in the current scope's time unit.
double ScaleScannedTime(double d, SimContext& ctx) {
  const TimeFormatSpec& tf = ctx.GetTimeFormat();
  double p = std::pow(10.0, tf.precision_number);
  // Round half up in the decimal sense; the epsilon absorbs binary
  // representation error so a decimal .5 boundary does not round down.
  double scaled = d * p;
  d = std::floor(scaled + 0.5 + std::fabs(scaled) * 1e-12) / p;
  const TimeScale& ts = ctx.CurrentTimeScale();
  d *= std::pow(10.0, tf.units_number - static_cast<int>(ts.unit));
  if (ts.magnitude != 0) d /= ts.magnitude;
  return d;
}

// §21.3.4.3: the real conversions (%f/%e/%g/%t) parse a floating-point token
// with strtod and store its IEEE-754 bit pattern. Overflow saturates to +Inf
// (or -Inf), which strtod yields directly, discharging the rule that a real
// destination too small for the converted input receives an infinity. %t
// additionally rescales the token under $timeformat.
ScanFieldResult ScanRealField(ScanCursor cur, int width, bool is_time,
                              Variable* var, SimContext& ctx, Arena& arena) {
  size_t limit = ScanUpperLimit(cur, width);
  std::string sub = cur.input.substr(cur.pos, limit - cur.pos);
  const char* c = sub.c_str();
  char* end = nullptr;
  double d = std::strtod(c, &end);
  if (end == c) return ScanFieldResult::kStop;
  cur.pos += static_cast<size_t>(end - c);
  if (is_time) d = ScaleScannedTime(d, ctx);
  StoreRealField(var, arena, d);
  return ScanFieldResult::kMatched;
}

// Reads a native-endian 32-bit word from the input.
uint32_t ScanRead32(const ScanCursor& cur, size_t at) {
  uint32_t x = 0;
  for (int b = 0; b < 4; ++b)
    x |= static_cast<uint32_t>(static_cast<uint8_t>(cur.input[at + b]))
         << (8 * b);
  return x;
}

// Mask selecting the bits of a 32-bit chunk that fall inside `width` starting
// at bit offset `off`.
uint32_t ScanChunkMask(uint32_t width, uint32_t off) {
  if (off + 32 <= width) return ~uint32_t{0};
  if (off >= width) return 0;
  return (uint32_t{1} << (width - off)) - 1;
}

// §21.3.4.3, Table 21-7: %u transfers unformatted 2-value binary data --
// enough to fill the destination -- as native-endian 32-bit chunks, the chunk
// holding the LSB first, mirroring the layout a matching $fwrite("%u", data)
// emits. The bytes are 2-value, so the stored value carries no x or z.
ScanFieldResult ScanRawBinaryField(ScanCursor cur, Variable* var,
                                   Arena& arena) {
  uint32_t w = var ? var->value.width : 32;
  uint32_t nchunks = (w + 31) / 32;
  if (nchunks == 0) nchunks = 1;
  size_t need = static_cast<size_t>(nchunks) * 4;
  if (cur.pos + need > cur.input.size())
    return ScanFieldResult::kStop;  // too little data to fill target
  auto vec = MakeLogic4VecVal(arena, w, 0);
  for (uint32_t k = 0; k < nchunks; ++k) {
    uint32_t off = k * 32;
    uint64_t chunk = ScanRead32(cur, cur.pos + k * 4) & ScanChunkMask(w, off);
    uint32_t word = off / 64;
    if (word < vec.nwords) vec.words[word].aval |= chunk << (off % 64);
  }
  cur.pos += need;
  if (var) var->value = vec;
  return ScanFieldResult::kMatched;
}

// §21.3.4.3, Table 21-7: %z transfers unformatted 4-value binary data as
// (aval, bval) 32-bit pairs in the s_vpi_vecval layout, LSB chunk first, each
// word native-endian -- the same layout $fwrite("%z", data) emits -- so x and
// z survive the round trip.
ScanFieldResult ScanFourStateField(ScanCursor cur, Variable* var,
                                   Arena& arena) {
  uint32_t w = var ? var->value.width : 32;
  uint32_t nchunks = (w + 31) / 32;
  if (nchunks == 0) nchunks = 1;
  size_t need = static_cast<size_t>(nchunks) * 8;
  if (cur.pos + need > cur.input.size())
    return ScanFieldResult::kStop;  // too little data to fill target
  auto vec = MakeLogic4VecVal(arena, w, 0);
  for (uint32_t k = 0; k < nchunks; ++k) {
    uint32_t off = k * 32;
    uint32_t mask = ScanChunkMask(w, off);
    uint64_t aval = ScanRead32(cur, cur.pos + k * 8) & mask;
    uint64_t bval = ScanRead32(cur, cur.pos + k * 8 + 4) & mask;
    uint32_t word = off / 64;
    if (word < vec.nwords) {
      vec.words[word].aval |= aval << (off % 64);
      vec.words[word].bval |= bval << (off % 64);
    }
  }
  cur.pos += need;
  if (var) var->value = vec;
  return ScanFieldResult::kMatched;
}

// §21.3.4.3, Table 21-7: %v matches a net signal strength as the
// three-character sequence of §21.2.1.4 (two strength letters and a logic
// value, e.g. "St1" or "HiZ"). The logic value -- the third character -- is
// converted to its 4-value equivalent and assigned; the strength letters are
// consumed but carry no storable information for a variable.
ScanFieldResult ScanStrengthField(ScanCursor cur, Variable* var, Arena& arena) {
  if (cur.pos + 3 > cur.input.size()) return ScanFieldResult::kStop;
  for (int k = 0; k < 3; ++k) {
    if (IsScanSpace(cur.input[cur.pos + k])) return ScanFieldResult::kStop;
  }
  char vc = cur.input[cur.pos + 2];
  bool a = false, b = false;
  if (vc == '1') {
    a = true;
  } else if (vc == 'x' || vc == 'X') {
    a = b = true;
  } else if (vc == 'z' || vc == 'Z') {
    b = true;
  } else if (vc != '0') {
    return ScanFieldResult::kStop;  // not a §21.2.1.4 logic value
  }
  cur.pos += 3;
  if (var) {
    auto vec = MakeLogic4VecVal(arena, var->value.width, 0);
    if (a) vec.words[0].aval |= 1;
    if (b) vec.words[0].bval |= 1;
    var->value = vec;
  }
  return ScanFieldResult::kMatched;
}

// Value of `c` as a digit of `base`, or -1 when it is not one.
int ScanDigitValue(char c, int base) {
  if (c >= '0' && c <= '9') {
    int v = c - '0';
    return v < base ? v : -1;
  }
  if (base == 16) {
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  }
  return -1;
}

// Table 21-7 unknown / high-impedance digit characters; ? is an alternative
// spelling of z.
bool ScanIsXZDigit(char c) {
  return c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?';
}

// One matched digit of a binary/octal/hex field: its value and 4-state kind.
struct ScanDigit {
  int val = 0;
  bool is_x = false;
  bool is_z = false;
};

// Packs base-2/8/16 digits (most significant first) into a 4-state value of
// the destination's width. Digits beyond the width are dropped from the top,
// discharging the rule that a too-small destination takes the LSBs.
void StoreScannedDigits(Variable* var, const std::vector<ScanDigit>& digits,
                        uint32_t bits_per_digit, Arena& arena) {
  if (!var) return;
  uint32_t w = var->value.width;
  auto vec = MakeLogic4VecVal(arena, w, 0);
  for (size_t i = 0; i < digits.size(); ++i) {
    const ScanDigit& d = digits[digits.size() - 1 - i];
    for (uint32_t b = 0; b < bits_per_digit; ++b) {
      uint32_t bit = static_cast<uint32_t>(i) * bits_per_digit + b;
      if (bit >= w) break;
      bool a = d.is_x || (!d.is_z && (((d.val >> b) & 1) != 0));
      bool bb = d.is_x || d.is_z;
      if (a) vec.words[bit / 64].aval |= uint64_t{1} << (bit % 64);
      if (bb) vec.words[bit / 64].bval |= uint64_t{1} << (bit % 64);
    }
  }
  var->value = vec;
}

// Fills every bit of the destination with x or with z, the reading of a
// decimal field that is a single value from the set x, X, z, Z, ?.
void StoreAllXZ(Variable* var, bool is_x, Arena& arena) {
  if (!var) return;
  uint32_t w = var->value.width;
  auto vec = MakeLogic4VecVal(arena, w, 0);
  for (uint32_t bit = 0; bit < w; ++bit) {
    if (is_x) vec.words[bit / 64].aval |= uint64_t{1} << (bit % 64);
    vec.words[bit / 64].bval |= uint64_t{1} << (bit % 64);
  }
  var->value = vec;
}

// §21.3.4.3, Table 21-7: a decimal field is an optionally signed digit string
// (underscores permitted after the first digit), or a single x/z/? standing
// for a wholly unknown or high-impedance value.
ScanFieldResult ScanDecimalField(ScanCursor cur, int width, Variable* var,
                                 Arena& arena) {
  size_t limit = ScanUpperLimit(cur, width);
  size_t p = cur.pos;
  bool neg = false;
  if (p < limit && (cur.input[p] == '+' || cur.input[p] == '-')) {
    neg = cur.input[p] == '-';
    ++p;
  }
  if (p < limit && ScanIsXZDigit(cur.input[p])) {
    char c = cur.input[p];
    cur.pos = p + 1;
    StoreAllXZ(var, c == 'x' || c == 'X', arena);
    return ScanFieldResult::kMatched;
  }
  uint64_t mag = 0;
  bool any = false;
  while (p < limit) {
    char c = cur.input[p];
    if (c == '_' && any) {
      ++p;
      continue;
    }
    if (c < '0' || c > '9') break;
    mag = mag * 10 + static_cast<uint64_t>(c - '0');
    any = true;
    ++p;
  }
  if (!any) return ScanFieldResult::kStop;  // sign alone converts nothing
  cur.pos = p;
  if (var) {
    uint64_t v = neg ? (0 - mag) : mag;
    var->value = MakeLogic4VecVal(arena, var->value.width, v);
  }
  return ScanFieldResult::kMatched;
}

// §21.3.4.3, Table 21-7: a binary, octal, or hexadecimal field is a sequence
// of base digits, x, z (or ?), and underscores; each digit -- including an x
// or z digit -- contributes its bit group to the 4-state result.
ScanFieldResult ScanIntegerField(ScanCursor cur, int base, int width,
                                 Variable* var, Arena& arena) {
  if (base == 10) return ScanDecimalField(cur, width, var, arena);
  size_t limit = ScanUpperLimit(cur, width);
  size_t p = cur.pos;
  std::vector<ScanDigit> digits;
  while (p < limit) {
    char c = cur.input[p];
    if (c == '_' && !digits.empty()) {
      ++p;
      continue;
    }
    int dv = ScanDigitValue(c, base);
    if (dv >= 0) {
      digits.push_back({dv, false, false});
      ++p;
      continue;
    }
    if (ScanIsXZDigit(c)) {
      digits.push_back({0, c == 'x' || c == 'X', !(c == 'x' || c == 'X')});
      ++p;
      continue;
    }
    break;
  }
  if (digits.empty()) return ScanFieldResult::kStop;
  cur.pos = p;
  uint32_t bits_per_digit = base == 2 ? 1 : (base == 8 ? 3 : 4);
  StoreScannedDigits(var, digits, bits_per_digit, arena);
  return ScanFieldResult::kMatched;
}

// Result of parsing one §21.3.4.3 (c) conversion specifier starting just after
// the '%'. `stop` requests ending the scan (the specifier ran off the end of
// the format string). On success `code` is the conversion letter and `fi` has
// been advanced to point at that letter.
struct ScanSpec {
  bool stop = false;
  bool suppress = false;
  int width = 0;
  char code = '\0';
};

// §21.3.4.3 (c): parse the optional assignment-suppression character and the
// optional maximum field width, then the conversion code. `fi` enters pointing
// at the character following '%' and exits pointing at the conversion letter.
ScanSpec ParseScanSpec(const std::string& fmt, size_t& fi) {
  ScanSpec spec;
  if (fmt[fi] == '*') {
    spec.suppress = true;
    if (++fi >= fmt.size()) {
      spec.stop = true;
      return spec;
    }
  }
  while (fi < fmt.size() && fmt[fi] >= '0' && fmt[fi] <= '9') {
    spec.width = spec.width * 10 + (fmt[fi] - '0');
    ++fi;
  }
  if (fi >= fmt.size()) {
    spec.stop = true;
    return spec;
  }
  spec.code = fmt[fi];
  return spec;
}

// Destination-argument list and binding state for one §21.3.4.3 scan. `dest`
// holds the `ndest` unevaluated destination expressions; `ai` is the index of
// the next destination to fill and `matched` counts assigned (non-suppressed)
// fields as they convert.
struct ScanArgs {
  Expr* const* dest;
  size_t ndest;
  SimContext& ctx;
  size_t ai = 0;
  uint32_t matched = 0;
};

// §21.3.4.3: resolve the destination that the next field assigns to. All
// members stay null when the field is suppressed, the arguments are exhausted,
// or the destination expression is not a plain identifier. A name that does
// not resolve to a variable may name an unpacked byte array (lowered to one
// element variable per index), which %s may fill.
ScanDest ResolveScanDest(ScanArgs& args, bool suppress) {
  ScanDest d;
  if (suppress || args.ai >= args.ndest) return d;
  const Expr* a = args.dest[args.ai];
  if (a == nullptr || a->kind != ExprKind::kIdentifier) return d;
  d.name = a->text;
  // An unpacked array is checked first: its lowering keeps per-element
  // variables (and possibly a placeholder under the bare name), so the bare
  // name must never be written as if it were the whole aggregate.
  const ArrayInfo* ai = args.ctx.FindArrayInfo(a->text);
  if (ai != nullptr) {
    if (!ai->is_dynamic && !ai->is_queue &&
        ai->elem_type_kind == DataTypeKind::kByte) {
      d.byte_array = ai;
    }
    return d;
  }
  d.var = args.ctx.FindVariable(a->text);
  if (d.var != nullptr) d.is_string = args.ctx.IsStringVariable(a->text);
  return d;
}

// §21.3.4.3: the integer format specifiers (h, d, o, b, c, u, and z) shall not
// be used with any unpacked aggregate data type.
bool IsIntegerClassCode(char lc) {
  return lc == 'h' || lc == 'x' || lc == 'd' || lc == 'o' || lc == 'b' ||
         lc == 'c' || lc == 'u' || lc == 'z';
}

// §21.3.4.3: dispatch a single conversion (other than the %% literal, which the
// caller handles) to the matching field handler. Leading white space is skipped
// for every code except %c and %m (which reads no input at all). Returns kStop
// on an unsupported conversion code.
ScanFieldResult DispatchScanField(char lc, const ScanCursor& cur, int width,
                                  const ScanDest& dst, SimContext& ctx,
                                  Arena& arena) {
  if (lc == 'c') {
    // §21.3.4.3: the character conversion does not skip leading white space.
    return ScanCharField(cur, width, dst, ctx, arena);
  }
  if (lc == 'm') {
    // §21.3.4.3, Table 21-7: %m assigns the current hierarchical path
    // (§21.2.1.5) as a string and reads nothing from the input.
    StoreScannedChars(dst, FormatDisplay("%m", {}, {.ctx = &ctx}), ctx, arena);
    return ScanFieldResult::kMatched;
  }
  // §21.3.4.3: every remaining conversion ignores leading white space.
  while (cur.pos < cur.input.size() && IsScanSpace(cur.input[cur.pos]))
    ++cur.pos;

  if (lc == 's') return ScanStringField(cur, width, dst, ctx, arena);
  if (lc == 'f' || lc == 'e' || lc == 'g' || lc == 't')
    return ScanRealField(cur, width, lc == 't', dst.var, ctx, arena);
  if (lc == 'u') return ScanRawBinaryField(cur, dst.var, arena);
  if (lc == 'z') return ScanFourStateField(cur, dst.var, arena);
  if (lc == 'v') return ScanStrengthField(cur, dst.var, arena);
  int base = SpecToBase(lc);
  if (base == 0) return ScanFieldResult::kStop;  // unsupported conversion code
  return ScanIntegerField(cur, base, width, dst.var, arena);
}

// §21.3.4.3 (c): handle one conversion specifier beginning at the '%' that `fi`
// currently points at. Advances `fi` past the specifier, mutates the cursor and
// `args` binding state, and returns false when the scan must stop (malformed
// specifier, %% mismatch, or a field that failed to convert).
bool HandleScanSpecifier(const std::string& fmt, size_t& fi,
                         const ScanCursor& cur, ScanArgs& args, Arena& arena) {
  if (fi + 1 >= fmt.size()) return false;
  ++fi;
  ScanSpec spec = ParseScanSpec(fmt, fi);
  if (spec.stop) return false;
  char lc = (spec.code >= 'A' && spec.code <= 'Z')
                ? static_cast<char>(spec.code - 'A' + 'a')
                : spec.code;

  if (lc == '%') {
    // §21.3.4.3: %% matches a literal '%' in the input.
    if (cur.pos >= cur.input.size() || cur.input[cur.pos] != '%') return false;
    ++cur.pos;
    return true;
  }

  ScanDest dst = ResolveScanDest(args, spec.suppress);
  // §21.3.4.3: the integer format specifiers shall not read into an unpacked
  // aggregate; only %s may fill an unpacked array of byte. Reject the misuse
  // with a diagnostic and end the scan without assigning.
  if (IsIntegerClassCode(lc) && !spec.suppress && args.ai < args.ndest) {
    const Expr* a = args.dest[args.ai];
    if (a != nullptr && a->kind == ExprKind::kIdentifier &&
        args.ctx.FindArrayInfo(a->text) != nullptr) {
      args.ctx.GetDiag().Warning({},
                                 std::string("$fscanf/$sscanf: %") + spec.code +
                                     " may not read into unpacked aggregate '" +
                                     std::string(a->text) + "'");
      return false;
    }
  }

  ScanFieldResult result =
      DispatchScanField(lc, cur, spec.width, dst, args.ctx, arena);
  if (result == ScanFieldResult::kStop) return false;
  if (result == ScanFieldResult::kMatched && !spec.suppress) {
    ++args.matched;
    ++args.ai;
  }
  return true;
}
}  // namespace

// §21.3.4.3 scan engine shared in spirit with $fscanf. Interprets `fmt` against
// `input`, assigning converted fields to the destination arguments; returns the
// count of assigned items and reports the consumed input length.
uint32_t RunScanf(const ScanRequest& req, SimContext& ctx, Arena& arena) {
  const std::string& input = req.input;
  const std::string& fmt = req.fmt;
  size_t pos = 0;
  ScanCursor cur{input, pos};
  ScanArgs args{req.dest, req.ndest, ctx};

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

    // §21.3.4.3 (c): a conversion specifier; stop the scan if it fails.
    if (!HandleScanSpecifier(fmt, fi, cur, args, arena)) break;
  }

  req.consumed = pos;
  return args.matched;
}

// §21.3.4.3: decode the str argument of $sscanf into the text to scan. The
// argument may be a string literal, a string or integral expression (decoded
// from its packed bytes, most significant first, dropping the all-zero high
// padding), or an unpacked array of byte read from its left bound. Null
// characters inside the text shall be considered white space for $sscanf, so
// each surviving NUL becomes a blank rather than vanishing (which would fuse
// the tokens on either side of it).
static std::string DecodeSscanfInput(const Expr* arg, SimContext& ctx,
                                     Arena& arena) {
  if (arg->kind == ExprKind::kStringLiteral) return ExtractStrArg(arg);
  if (arg->kind == ExprKind::kIdentifier) {
    const ArrayInfo* ai = ctx.FindArrayInfo(arg->text);
    if (ai != nullptr && !ai->is_dynamic && !ai->is_queue &&
        ai->elem_type_kind == DataTypeKind::kByte) {
      std::string s;
      for (uint32_t i = 0; i < ai->size; ++i) {
        uint32_t idx =
            ai->is_descending ? (ai->lo + ai->size - 1 - i) : (ai->lo + i);
        std::string ename =
            std::string(arg->text) + "[" + std::to_string(idx) + "]";
        Variable* elem = ctx.FindVariable(ename);
        char c = elem ? static_cast<char>(elem->value.ToUint64() & 0xFF) : 0;
        s += c != 0 ? c : ' ';
      }
      return s;
    }
  }
  auto val = EvalExpr(arg, ctx, arena);
  uint32_t nbytes = val.width / 8;
  std::string result;
  bool started = false;
  for (uint32_t i = nbytes; i > 0; --i) {
    uint32_t byte_idx = i - 1;
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    if (word >= val.nwords) continue;
    auto ch = static_cast<char>((val.words[word].aval >> bit) & 0xFF);
    if (!started && ch == 0) continue;  // leading NUL padding, not content
    started = true;
    result += ch != 0 ? ch : ' ';
  }
  return result;
}

static Logic4Vec EvalSscanf(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 3) return MakeLogic4VecVal(arena, 32, 0);

  // §21.3.4.3: when the str argument or the format string carries an unknown
  // bit (x or z), $sscanf reports EOF (-1).
  if (ScanArgHasUnknownBits(expr->args[0], ctx, arena) ||
      ScanArgHasUnknownBits(expr->args[1], ctx, arena)) {
    return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);
  }

  std::string input = DecodeSscanfInput(expr->args[0], ctx, arena);
  // §21.3.4.3: the format can be an expression -- a string literal, a string
  // data type, or an integral data type whose content is the control string.
  std::string fmt = ResolveFormatArg(expr->args[1], ctx, arena);

  size_t consumed = 0;
  ScanRequest req{input, fmt, expr->args.data() + 2, expr->args.size() - 2,
                  consumed};
  uint32_t matched = RunScanf(req, ctx, arena);

  // §21.3.4.3: zero signals a matching failure against present input, while EOF
  // (-1) is returned when the input is exhausted before any field converts.
  if (matched == 0) {
    size_t p = consumed;
    while (p < input.size() && IsScanSpace(input[p])) ++p;
    if (p >= input.size()) return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);
  }
  return MakeLogic4VecVal(arena, 32, matched);
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
  // §D.14: the string-loading counterparts of $readmemh / $readmemb.
  if (name == "$sreadmemh") return EvalSreadmem(expr, ctx, arena, true);
  if (name == "$sreadmemb") return EvalSreadmem(expr, ctx, arena, false);
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

}  // namespace delta
