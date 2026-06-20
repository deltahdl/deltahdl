#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "parser/ast.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
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
  std::string output = BuildStringTaskOutput(rest, default_radix, ctx, arena);
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
  std::string out = FormatDisplay(fmt, vals, {.ctx = &ctx});
  if (dst) dst->value = StringToLogic4Vec(arena, out);
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
    std::fputs(output.c_str(), fp);
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

// §21.3.4.3: the character conversion does not skip leading white space; it
// copies `width` (default 1) raw characters into the destination.
ScanFieldResult ScanCharField(ScanCursor cur, int width, Variable* var,
                              Arena& arena) {
  int cnt = width > 0 ? width : 1;
  if (cur.pos >= cur.input.size()) return ScanFieldResult::kStop;
  std::string chars;
  for (int k = 0; k < cnt && cur.pos < cur.input.size(); ++k)
    chars += cur.input[cur.pos++];
  if (var) {
    if (chars.size() == 1) {
      var->value = MakeLogic4VecVal(arena, var->value.width,
                                    static_cast<uint8_t>(chars[0]));
    } else {
      var->value = ScanStringToVec(arena, chars, var->value.width);
    }
  }
  return ScanFieldResult::kMatched;
}

// §21.3.4.3: %s gathers a run of non-white-space characters (bounded by the
// field width) into the destination.
ScanFieldResult ScanStringField(ScanCursor cur, int width, Variable* var,
                                Arena& arena) {
  size_t limit = ScanUpperLimit(cur, width);
  std::string s;
  while (cur.pos < limit && !IsScanSpace(cur.input[cur.pos]))
    s += cur.input[cur.pos++];
  if (s.empty()) return ScanFieldResult::kStop;
  if (var) var->value = ScanStringToVec(arena, s, var->value.width);
  return ScanFieldResult::kMatched;
}

// §21.3.4.3: the real conversions (%f/%e/%g/%t) parse a floating-point token
// with strtod and store its IEEE-754 bit pattern.
ScanFieldResult ScanRealField(ScanCursor cur, int width, Variable* var,
                              Arena& arena) {
  size_t limit = ScanUpperLimit(cur, width);
  std::string sub = cur.input.substr(cur.pos, limit - cur.pos);
  const char* c = sub.c_str();
  char* end = nullptr;
  double d = std::strtod(c, &end);
  if (end == c) return ScanFieldResult::kStop;
  cur.pos += static_cast<size_t>(end - c);
  StoreRealField(var, arena, d);
  return ScanFieldResult::kMatched;
}

// §21.3.4.3, Table 21-7: %u transfers unformatted 2-value binary data, pulling
// enough raw bytes to fill the destination in the host's native (little-endian)
// byte order. The bytes are known, so the stored value carries no x or z.
ScanFieldResult ScanRawBinaryField(ScanCursor cur, Variable* var,
                                   Arena& arena) {
  uint32_t w = var ? var->value.width : 8;
  size_t nbytes = (w + 7) / 8;
  if (cur.pos + nbytes > cur.input.size())
    return ScanFieldResult::kStop;  // too little data to fill target
  uint64_t v = 0;
  for (size_t k = 0; k < nbytes && k < sizeof(uint64_t); ++k) {
    v |= static_cast<uint64_t>(static_cast<uint8_t>(cur.input[cur.pos + k]))
         << (8 * k);
  }
  cur.pos += nbytes;
  if (var) var->value = MakeLogic4VecVal(arena, var->value.width, v);
  return ScanFieldResult::kMatched;
}

// §21.3.4.3: the integer conversions (%d/%h/%x/%b/%o) parse a token in the
// base named by the specifier and store it into the destination.
ScanFieldResult ScanIntegerField(ScanCursor cur, int base, int width,
                                 Variable* var, Arena& arena) {
  size_t limit = ScanUpperLimit(cur, width);
  std::string sub = cur.input.substr(cur.pos, limit - cur.pos);
  const char* c = sub.c_str();
  char* end = nullptr;
  unsigned long long v = std::strtoull(c, &end, base);
  if (end == c) return ScanFieldResult::kStop;
  cur.pos += static_cast<size_t>(end - c);
  if (var) {
    var->value =
        MakeLogic4VecVal(arena, var->value.width, static_cast<uint64_t>(v));
  }
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

// §21.3.4.3: resolve the Variable* that the next field assigns to, or nullptr
// when the field is suppressed, the arguments are exhausted, or the destination
// expression is not a plain identifier.
Variable* ResolveScanVar(ScanArgs& args, bool suppress) {
  if (suppress || args.ai >= args.ndest) return nullptr;
  const Expr* a = args.dest[args.ai];
  if (a->kind == ExprKind::kIdentifier) return args.ctx.FindVariable(a->text);
  return nullptr;
}

// §21.3.4.3: dispatch a single conversion (other than the %% literal, which the
// caller handles) to the matching field handler. Leading white space is skipped
// for every code except %c. Returns kStop on an unsupported conversion code.
ScanFieldResult DispatchScanField(char lc, const ScanCursor& cur, int width,
                                  Variable* var, Arena& arena) {
  if (lc == 'c') {
    // §21.3.4.3: the character conversion does not skip leading white space.
    return ScanCharField(cur, width, var, arena);
  }
  // §21.3.4.3: every remaining conversion ignores leading white space.
  while (cur.pos < cur.input.size() && IsScanSpace(cur.input[cur.pos]))
    ++cur.pos;

  if (lc == 's') return ScanStringField(cur, width, var, arena);
  if (lc == 'f' || lc == 'e' || lc == 'g' || lc == 't')
    return ScanRealField(cur, width, var, arena);
  if (lc == 'u') return ScanRawBinaryField(cur, var, arena);
  int base = SpecToBase(lc);
  if (base == 0) return ScanFieldResult::kStop;  // unsupported conversion code
  return ScanIntegerField(cur, base, width, var, arena);
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

  ScanFieldResult result = DispatchScanField(
      lc, cur, spec.width, ResolveScanVar(args, spec.suppress), arena);
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
