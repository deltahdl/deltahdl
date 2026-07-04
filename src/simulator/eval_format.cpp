#include <cstdint>
#include <cstdio>
#include <cstring>
#include <string>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"

namespace delta {

struct FormatArgs {
  const std::vector<Logic4Vec>& vals;
  size_t vi = 0;
  const std::vector<std::string>& p_fmts;
  const TimeFormatSpec* time_format = nullptr;
  const std::vector<std::string>& v_fmts;
  SimContext* ctx = nullptr;
};

// §21.2.1.5: build the hierarchical name that %m expands to -- the name of the
// design element, subroutine, named block, or labeled statement that contains
// the system task being run. The name starts at the top-level module and walks
// down through the chain of instance names recorded on the running process,
// then through the active subroutine / named-block / labeled-statement scopes
// that the statement executor tracks in lexical-nesting order.
static std::string BuildScopeHierName(SimContext* ctx) {
  if (ctx == nullptr) return "";
  // The empty instance prefix is the top level; its registered type name is the
  // top module's name, which doubles as the top instance name for %m.
  std::string name(ctx->FindInstanceType(""));
  if (Process* proc = ctx->CurrentProcess()) {
    std::string prefix = proc->inst_prefix;  // "u1.u2." form, empty at top
    if (!prefix.empty() && prefix.back() == '.') prefix.pop_back();
    if (!prefix.empty()) {
      if (!name.empty()) name += '.';
      name += prefix;
    }
  }
  for (std::string_view scope : ctx->ActiveNamedScopes()) {
    if (!name.empty()) name += '.';
    name += std::string(scope);
  }
  return name;
}

// §33.7: build the "library.cell" string that %l / %L expands to -- the actual
// library and cell bound to the module instance that contains the running
// display task. Like %m (which reports that instance's hierarchical name), the
// instance is the one named by the running process's instance prefix; the
// lowerer records each instance's resolved binding under that same prefix. When
// there is no simulation context, or the containing instance has no recorded
// binding, the specifier still substitutes a generic library.cell token so it
// never expands to nothing (the no-argument substitution rule of §21.2.1).
static std::string BuildInstanceBinding(SimContext* ctx) {
  if (ctx != nullptr) {
    std::string prefix;
    if (Process* proc = ctx->CurrentProcess()) {
      prefix = proc->inst_prefix;  // "u1.u2." form, empty at the top level
      if (!prefix.empty() && prefix.back() == '.') prefix.pop_back();
    }
    std::string_view binding = ctx->FindInstanceBinding(prefix);
    if (!binding.empty()) return std::string(binding);
  }
  return "<library.cell>";
}

std::string FormatValueAsString(const Logic4Vec& val) {
  std::string result;
  uint32_t nbytes = (val.width + 7) / 8;
  for (uint32_t i = nbytes; i > 0; --i) {
    uint32_t byte_offset = (i - 1) * 8;
    uint32_t word = byte_offset / 64;
    uint32_t bit = byte_offset % 64;
    uint64_t aval = (word < val.nwords) ? val.words[word].aval : 0;
    auto ch = static_cast<char>((aval >> bit) & 0xFF);
    if (ch != 0) result += ch;
  }
  return result;
}

static std::string FormatValueAsReal(const Logic4Vec& val, char spec) {
  uint64_t bits = val.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &bits, sizeof(double));
  char buf[128];
  if (spec == 'e') {
    std::snprintf(buf, sizeof(buf), "%e", d);
  } else if (spec == 'g') {
    std::snprintf(buf, sizeof(buf), "%g", d);
  } else {
    std::snprintf(buf, sizeof(buf), "%f", d);
  }
  return buf;
}

static std::string FormatRealAsInt(const Logic4Vec& val) {
  uint64_t v = val.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &v, sizeof(double));
  char buf[64];
  std::snprintf(buf, sizeof(buf), "%lld", static_cast<long long>(d));
  return buf;
}

static std::string FormatDecimal(const Logic4Vec& val) {
  uint64_t v = val.ToUint64();
  char buf[64];
  if (val.is_signed) {
    auto sv = static_cast<int64_t>(v);
    if (val.width < 64) {
      uint64_t sign_bit = uint64_t{1} << (val.width - 1);
      if (v & sign_bit)
        sv = static_cast<int64_t>(v | (~uint64_t{0} << val.width));
    }
    std::snprintf(buf, sizeof(buf), "%lld", static_cast<long long>(sv));
  } else {
    std::snprintf(buf, sizeof(buf), "%llu", static_cast<unsigned long long>(v));
  }
  return buf;
}

// §21.2.1.3: a bit-range classification used by the decimal, hexadecimal, and
// octal renderings to decide whether unknown (x) or high-impedance (z) bits
// force a status character in place of the ordinary digit.
enum class XZClass : std::uint8_t { kKnown, kAllX, kAllZ, kSomeX, kSomeZ };

// Read the (aval, bval) pair of a single bit out of a 4-state vector. The
// encoding matches Logic4Vec::ToString (canonical, Figure 38-8): bval clear is
// a known bit, bval set with aval set is x, and bval set with aval clear is z.
static void ReadBit(const Logic4Vec& val, uint32_t i, bool& a, bool& b) {
  uint32_t w = i / 64;
  uint64_t mask = uint64_t{1} << (i % 64);
  a = (val.words[w].aval & mask) != 0;
  b = (val.words[w].bval & mask) != 0;
}

// §21.2.1.3: examine the bits in [lo, hi) and report which display rule
// applies. A fully unknown range maps to a lowercase x and a fully
// high-impedance range to a lowercase z. Any mix of states yields an uppercase
// character: an unknown bit always wins (uppercase X), and only a
// high-impedance bit with no unknown bit present yields uppercase Z.
static XZClass ClassifyBits(const Logic4Vec& val, uint32_t lo, uint32_t hi) {
  bool has_known = false, has_x = false, has_z = false;
  for (uint32_t i = lo; i < hi; ++i) {
    bool a = false, b = false;
    ReadBit(val, i, a, b);
    if (!b)
      has_known = true;
    else if (a)
      has_x = true;
    else
      has_z = true;
  }
  if (!has_x && !has_z) return XZClass::kKnown;
  if (has_x && !has_z && !has_known) return XZClass::kAllX;
  if (has_z && !has_x && !has_known) return XZClass::kAllZ;
  return has_x ? XZClass::kSomeX : XZClass::kSomeZ;
}

// Maps a non-known classification to its display character. Returns 0 for a
// known group, signalling that the caller should render the ordinary value.
static char XZDigitChar(XZClass c) {
  switch (c) {
    case XZClass::kAllX:
      return 'x';
    case XZClass::kAllZ:
      return 'z';
    case XZClass::kSomeX:
      return 'X';
    case XZClass::kSomeZ:
      return 'Z';
    default:
      return 0;
  }
}

// §21.2.1.3: render a value in hexadecimal (group_size 4) or octal
// (group_size 3). Each group of bits collapses to a single digit; a group that
// carries any x or z bit follows the status-character rules above instead of
// the plain radix value. Fully known values reproduce the auto-sized,
// leading-zero rendering of FormatArg.
static std::string FormatRadixXZ(const Logic4Vec& val, uint32_t group_size) {
  uint32_t ndigits = (val.width + group_size - 1) / group_size;
  if (ndigits == 0) ndigits = 1;
  std::string out;
  out.reserve(ndigits);
  for (uint32_t d = ndigits; d > 0; --d) {
    uint32_t lo = (d - 1) * group_size;
    uint32_t hi = lo + group_size;
    if (hi > val.width) hi = val.width;
    char xz = XZDigitChar(ClassifyBits(val, lo, hi));
    if (xz != 0) {
      out += xz;
      continue;
    }
    uint32_t digit = 0;
    for (uint32_t i = lo; i < hi; ++i) {
      bool a = false, b = false;
      ReadBit(val, i, a, b);
      if (a) digit |= (1u << (i - lo));
    }
    out += static_cast<char>(digit < 10 ? '0' + digit : 'a' + digit - 10);
  }
  return out;
}

// §21.2.1.3: a decimal field shows a single status character when the value
// holds unknown or high-impedance bits, rather than a numeral.
static std::string FormatDecimalXZ(const Logic4Vec& val) {
  char xz = XZDigitChar(ClassifyBits(val, 0, val.width));
  if (xz != 0) return std::string(1, xz);
  return FormatDecimal(val);
}

// Apply the $timeformat configuration (20.4.3) to a raw time value. The
// number is rendered with the configured decimal precision, padded with
// leading spaces to the minimum field width, and tagged with the suffix
// string.
std::string FormatTimeUnderTimeformat(const Logic4Vec& val,
                                      const TimeFormatSpec& spec) {
  auto ticks = static_cast<double>(val.ToUint64());
  char buf[64];
  std::snprintf(buf, sizeof(buf), "%.*f", spec.precision_number, ticks);
  std::string body(buf);
  int pad = spec.minimum_field_width -
            static_cast<int>(body.size() + spec.suffix_string.size());
  std::string out;
  if (pad > 0) out.assign(static_cast<size_t>(pad), ' ');
  out += body;
  out += spec.suffix_string;
  return out;
}

std::string FormatArg(const Logic4Vec& val, char spec) {
  // Table 21-1 and Table 21-2 spell every specifier as "%x or %X", so the
  // dispatch below works in a single case after this normalization.
  if (spec >= 'A' && spec <= 'Z') spec = static_cast<char>(spec - 'A' + 'a');

  if (val.is_real && spec == 'd') return FormatRealAsInt(val);

  uint64_t v = val.ToUint64();
  char buf[64];
  switch (spec) {
    case 'd':
      // §21.2.1.3: decimal renders a status character for unknown/high-Z bits.
      return FormatDecimalXZ(val);
    case 'h':
    case 'x':
      // §21.2.1.3: each group of four bits is one hex digit, with x/z groups
      // rendered per the unknown/high-impedance rules.
      return FormatRadixXZ(val, 4);
    case 'o':
      // §21.2.1.3: octal groups three bits per digit, otherwise as for hex.
      return FormatRadixXZ(val, 3);
    case 'b':
      return val.ToString();
    case 'c':
      return std::string(1, static_cast<char>(v & 0xFF));
    case 't':
      std::snprintf(buf, sizeof(buf), "%llu",
                    static_cast<unsigned long long>(v));
      return buf;
    case 's':
      return FormatValueAsString(val);
    case 'e':
    case 'f':
    case 'g':
      return FormatValueAsReal(val, spec);
    default:
      // A specifier that does not appear in Table 21-1 or Table 21-2 is a
      // misuse of the format string. Surface it to stderr so a test or a
      // user can see what was wrong, and leave the unrecognized pair in the
      // output stream so the misuse does not silently masquerade as a
      // valid rendering of the value.
      std::fprintf(stderr, "[deltahdl] unknown format specifier: %%%c\n", spec);
      return std::string("%") + spec;
  }
}

// Table 21-4 maps each strength level (0..7, the numeric value of the
// Strength enum) to its two-letter mnemonic.
static const char* StrengthMnemonic(uint8_t level) {
  static const char* k_mnemonics[8] = {"Hi", "Sm", "Me", "We",
                                       "La", "Pu", "St", "Su"};
  return k_mnemonics[level & 0x7];
}

// Renders the three-character strength format of a scalar net. The first two
// characters describe the strength -- a Table 21-4 mnemonic when the level is a
// single point, or a pair of decimal digits when a range of levels applies.
// The third character is the logic value drawn from Table 21-3.
std::string FormatStrength(const NetStrength& ns) {
  auto s0_hi = static_cast<uint8_t>(ns.s0_hi);
  auto s0_lo = static_cast<uint8_t>(ns.s0_lo);
  auto s1_hi = static_cast<uint8_t>(ns.s1_hi);
  auto s1_lo = static_cast<uint8_t>(ns.s1_lo);

  // A side "drives" when its strongest component is above the highz level.
  bool drives0 = s0_hi != 0;
  bool drives1 = s1_hi != 0;

  // Neither side drives: the net floats. The high-impedance strength admits
  // only the Z logic value, and its level is always the Hi mnemonic.
  if (!drives0 && !drives1) return "HiZ";

  // Both sides drive: the resolved logic value is unknown (X). A mnemonic is
  // used only when the 0 and 1 components share one common strength level;
  // otherwise the 0-side and 1-side levels print as two decimal digits.
  if (drives0 && drives1) {
    if (s0_hi == s0_lo && s1_hi == s1_lo && s0_hi == s1_hi) {
      return std::string(StrengthMnemonic(s0_hi)) + "X";
    }
    return std::string(1, static_cast<char>('0' + s0_hi)) +
           static_cast<char>('0' + s1_hi) + "X";
  }

  // Exactly one side drives; take that side's level range and known value.
  uint8_t hi = drives0 ? s0_hi : s1_hi;
  uint8_t lo = drives0 ? s0_lo : s1_lo;
  char known = drives0 ? '0' : '1';

  // A range reaching down to highz means the value is ambiguous between the
  // driven level and a float: L (0 or Z) or H (1 or Z). Both always use a
  // mnemonic to name the strength level.
  if (lo == 0) {
    char ambiguous = drives0 ? 'L' : 'H';
    return std::string(StrengthMnemonic(hi)) + ambiguous;
  }

  // A single level uses its mnemonic; a genuine range prints the maximum and
  // minimum levels as two decimal digits.
  if (hi == lo) return std::string(StrengthMnemonic(hi)) + known;
  return std::string(1, static_cast<char>('0' + hi)) +
         static_cast<char>('0' + lo) + known;
}

// §21.2.1.2: the minimal-width ("significant figures") rendering of a value for
// a given radix, before any explicit field width is applied. The decimal,
// string, and character forms already carry no leading fill, so they defer to
// the auto-sized rendering; the hex/octal/binary radices, whose auto rendering
// pads out to the full bit width with leading zeros, drop those zeros here.
static std::string FormatArgMinimal(const Logic4Vec& val, char spec) {
  uint64_t v = val.ToUint64();
  char buf[64];
  switch (spec) {
    case 'h':
    case 'x':
      // §21.2.1.3 status characters carry meaning that cannot be stripped down
      // to a "significant digit", so a value bearing x/z keeps its full digit
      // string; only purely known values get the minimal rendering.
      if (!val.IsKnown()) return FormatRadixXZ(val, 4);
      std::snprintf(buf, sizeof(buf), "%llx",
                    static_cast<unsigned long long>(v));
      return buf;
    case 'o':
      if (!val.IsKnown()) return FormatRadixXZ(val, 3);
      std::snprintf(buf, sizeof(buf), "%llo",
                    static_cast<unsigned long long>(v));
      return buf;
    case 'b': {
      // Each bit prints separately; trim only the leading zeros, keeping at
      // least one character so a zero value still shows a digit.
      std::string full = val.ToString();
      size_t start = full.find_first_not_of('0');
      if (start == std::string::npos) return "0";
      return full.substr(start);
    }
    default:
      return FormatArg(val, spec);
  }
}

// §21.2.1.2: render a value while honoring an explicit field width taken from
// the format specifier (e.g. "%3d" or "%0h"). With no width the value is
// auto-sized exactly as FormatArg does. A width of zero selects the minimum
// width with no leading fill. A non-zero width left-pads the minimal rendering
// to that many columns -- spaces for the decimal, string, and character forms,
// leading zeros for the hex/octal/binary radices. A value already wider than
// the field is expanded rather than truncated.
static std::string FormatArgWidth(const Logic4Vec& val, char spec,
                                  bool has_width, uint32_t width) {
  if (!has_width) return FormatArg(val, spec);

  char norm = spec;
  if (norm >= 'A' && norm <= 'Z') norm = static_cast<char>(norm - 'A' + 'a');

  // The real and time renderings are sized by their own rules, not by this
  // subclause; leave them to the auto-sized path.
  if (norm == 'e' || norm == 'f' || norm == 'g' || norm == 't')
    return FormatArg(val, spec);

  std::string core = FormatArgMinimal(val, norm);
  if (width == 0 || core.size() >= width) return core;

  char pad =
      (norm == 'h' || norm == 'x' || norm == 'o' || norm == 'b') ? '0' : ' ';
  return std::string(width - core.size(), pad) + core;
}

static int FormatHexDigitVal(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

// §21.2.1: inside a $display/$write string-literal argument the special
// character '\' introduces an escape whose meaning is that of Table 5-1 in
// 5.9.1. Decode a single such sequence in place -- named escapes, octal '\ddd'
// and hex '\xhh' -- and emit the resulting byte as a literal. Decoding here,
// one character at a time, keeps an escaped byte (e.g. octal '\045') out of the
// '%' format-specifier machinery even when it decodes to a '%'. Any other
// escaped character stands for itself, matching the string-literal decoder.
static void AppendLiteralChar(const std::string& fmt, size_t& i,
                              std::string& out) {
  if (fmt[i] != '\\' || i + 1 >= fmt.size()) {
    out += fmt[i];
    return;
  }
  char c = fmt[++i];
  switch (c) {
    case 'n':
      out += '\n';
      return;
    case 't':
      out += '\t';
      return;
    case '\\':
      out += '\\';
      return;
    case '"':
      out += '"';
      return;
    case 'v':
      out += '\v';
      return;
    case 'f':
      out += '\f';
      return;
    case 'a':
      out += '\a';
      return;
    default:
      break;
  }
  if (c == 'x') {
    int val = 0;
    for (int j = 0;
         j < 2 && i + 1 < fmt.size() && FormatHexDigitVal(fmt[i + 1]) >= 0; ++j)
      val = val * 16 + FormatHexDigitVal(fmt[++i]);
    out += static_cast<char>(val);
    return;
  }
  if (c >= '0' && c <= '7') {
    int val = c - '0';
    for (int j = 0;
         j < 2 && i + 1 < fmt.size() && fmt[i + 1] >= '0' && fmt[i + 1] <= '7';
         ++j)
      val = val * 8 + (fmt[++i] - '0');
    out += static_cast<char>(val);
    return;
  }
  out += c;
}

// §21.2.1.2: parse the optional field width that may sit between the '%' and
// the radix letter. It shall be a non-negative decimal integer constant.
// Starting at fmt[start] (the character after the '%'), advance past the run of
// digits and report whether any were seen along with their value; leave start
// pointing at the first non-digit (the radix letter).
static void ParseFieldWidth(const std::string& fmt, size_t& start,
                            bool& has_width, uint32_t& width) {
  has_width = false;
  width = 0;
  while (start < fmt.size() && fmt[start] >= '0' && fmt[start] <= '9') {
    has_width = true;
    width = width * 10 + static_cast<uint32_t>(fmt[start] - '0');
    ++start;
  }
}

// Specifiers that take no expression argument (%m, %l) substitute a scope-
// derived token directly. Returns true when the spec was handled here; the
// caller then leaves the argument cursor untouched.
static bool TryNoArgScopeSpec(char spec, FormatArgs& args, std::string& out) {
  // §21.2.1.5: %m expands to the hierarchical name of the scope that invokes
  // the system task.
  if (spec == 'm') {
    out += BuildScopeHierName(args.ctx);
    return true;
  }
  // §33.7: %l / %L expand to the library.cell binding of the module instance
  // that contains the display task, consuming no argument the way %m does.
  if (spec == 'l') {
    out += BuildInstanceBinding(args.ctx);
    return true;
  }
  return false;
}

// Specifiers whose substitution is precomputed by the calling task and held in
// a parallel string vector indexed by the argument cursor: %v (§21.2.1.4 net
// strength) and %p (assignment-pattern rendering). Returns true when the spec
// was handled here; in that case the argument cursor has been advanced.
static bool TryPrecomputedArgSpec(char spec, FormatArgs& args,
                                  std::string& out) {
  // §21.2.1.4: %v prints the strength of a scalar net. Each %v consumes one
  // argument; the strength string is precomputed by the calling task, which
  // holds the net reference, and is substituted verbatim here.
  if (spec == 'v') {
    if (args.vi < args.v_fmts.size() && !args.v_fmts[args.vi].empty()) {
      out += args.v_fmts[args.vi];
    }
    ++args.vi;
    return true;
  }
  if (spec == 'p' && args.vi < args.p_fmts.size() &&
      !args.p_fmts[args.vi].empty()) {
    out += args.p_fmts[args.vi];
    ++args.vi;
    return true;
  }
  return false;
}

// Render the next value argument for an ordinary radix/real/time specifier,
// advancing the argument cursor when a value is consumed.
static void AppendValueArg(char spec, bool has_width, uint32_t width,
                           FormatArgs& args, std::string& out) {
  if (args.vi < args.vals.size()) {
    if (spec == 't' && args.time_format != nullptr) {
      out += FormatTimeUnderTimeformat(args.vals[args.vi++], *args.time_format);
    } else {
      out += FormatArgWidth(args.vals[args.vi++], spec, has_width, width);
    }
  }
}

static bool ProcessFormatSpec(const std::string& fmt, size_t& i,
                              FormatArgs& args, std::string& out) {
  if (fmt[i + 1] == '%') {
    out += '%';
    ++i;
    return false;
  }

  size_t j = i + 1;
  bool has_width = false;
  uint32_t width = 0;
  ParseFieldWidth(fmt, j, has_width, width);
  char spec = (j < fmt.size()) ? fmt[j] : 'd';

  // Table 21-1 and Table 21-2 give each specifier in both cases (e.g.
  // "%m or %M"); collapse to a single case before deciding what to do.
  if (spec >= 'A' && spec <= 'Z') spec = static_cast<char>(spec - 'A' + 'a');

  // No-argument scope specifiers leave the argument cursor untouched, so report
  // false to the caller.
  if (TryNoArgScopeSpec(spec, args, out)) {
    i = j;
    return false;
  }

  if (TryPrecomputedArgSpec(spec, args, out)) {
    i = j;
    return true;
  }

  AppendValueArg(spec, has_width, width, args, out);
  i = j;
  return true;
}

std::string FormatDisplay(const std::string& fmt,
                          const std::vector<Logic4Vec>& vals,
                          const DisplayFormatOpts& opts) {
  std::string out;
  // §21.2.1.4 / §21.2.1: a null precomputed-string pointer means the calling
  // task supplied none, so bind the argument cursor to a shared empty list.
  static const std::vector<std::string> kEmpty;
  const std::vector<std::string>& p_fmts =
      opts.p_fmts != nullptr ? *opts.p_fmts : kEmpty;
  const std::vector<std::string>& v_fmts =
      opts.v_fmts != nullptr ? *opts.v_fmts : kEmpty;
  FormatArgs args{vals, 0, p_fmts, opts.time_format, v_fmts, opts.ctx};
  for (size_t i = 0; i < fmt.size(); ++i) {
    if (fmt[i] != '%' || i + 1 >= fmt.size()) {
      AppendLiteralChar(fmt, i, out);
      continue;
    }
    ProcessFormatSpec(fmt, i, args, out);
  }
  return out;
}

std::string ExtractFormatString(const Expr* first_arg) {
  auto text = first_arg->text;
  if (text.size() >= 2 && text.front() == '"') {
    return std::string(text.substr(1, text.size() - 2));
  }
  return std::string(text);
}

}  // namespace delta
