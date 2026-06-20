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
  std::string out = FormatDisplay(fmt, vals, {}, nullptr, {}, &ctx);
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
static Logic4Vec ScanStringToVec(Arena& arena, const std::string& str,
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
