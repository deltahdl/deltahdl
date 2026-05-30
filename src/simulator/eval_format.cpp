#include <cstdio>
#include <cstring>
#include <string>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

struct FormatArgs {
  const std::vector<Logic4Vec>& vals;
  size_t vi = 0;
  const std::vector<std::string>& p_fmts;
  const TimeFormatSpec* time_format = nullptr;
  const std::vector<std::string>& v_fmts;
};

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

// Apply the $timeformat configuration (20.4.3) to a raw time value. The
// number is rendered with the configured decimal precision, padded with
// leading spaces to the minimum field width, and tagged with the suffix
// string.
std::string FormatTimeUnderTimeformat(const Logic4Vec& val,
                                      const TimeFormatSpec& spec) {
  double ticks = static_cast<double>(val.ToUint64());
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
      return FormatDecimal(val);
    case 'h':
    case 'x': {

      uint32_t ndigits = (val.width + 3) / 4;
      if (ndigits == 0) ndigits = 1;
      std::snprintf(buf, sizeof(buf), "%0*llx", static_cast<int>(ndigits),
                    static_cast<unsigned long long>(v));
      return buf;
    }
    case 'o': {

      uint32_t ndigits = (val.width + 2) / 3;
      if (ndigits == 0) ndigits = 1;
      std::snprintf(buf, sizeof(buf), "%0*llo", static_cast<int>(ndigits),
                    static_cast<unsigned long long>(v));
      return buf;
    }
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
      std::fprintf(stderr, "[deltahdl] unknown format specifier: %%%c\n",
                   spec);
      return std::string("%") + spec;
  }
}

// Table 21-4 maps each strength level (0..7, the numeric value of the
// Strength enum) to its two-letter mnemonic.
static const char* StrengthMnemonic(uint8_t level) {
  static const char* kMnemonics[8] = {"Hi", "Sm", "Me", "We",
                                      "La", "Pu", "St", "Su"};
  return kMnemonics[level & 0x7];
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

static void AppendLiteralChar(const std::string& fmt, size_t& i,
                              std::string& out) {
  if (fmt[i] == '\\' && i + 1 < fmt.size()) {
    out += (fmt[i + 1] == 'n') ? '\n' : fmt[i + 1];
    ++i;
  } else {
    out += fmt[i];
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
  while (j < fmt.size() && (fmt[j] >= '0' && fmt[j] <= '9')) ++j;
  char spec = (j < fmt.size()) ? fmt[j] : 'd';

  // Table 21-1 and Table 21-2 give each specifier in both cases (e.g.
  // "%m or %M"); collapse to a single case before deciding what to do.
  if (spec >= 'A' && spec <= 'Z') spec = static_cast<char>(spec - 'A' + 'a');

  if (spec == 'm') {
    out += "<module>";
    i = j;
    return false;
  }

  if (spec == 'l') {
    out += "<library.cell>";
    i = j;
    return false;
  }

  // §21.2.1.4: %v prints the strength of a scalar net. Each %v consumes one
  // argument; the strength string is precomputed by the calling task, which
  // holds the net reference, and is substituted verbatim here.
  if (spec == 'v') {
    if (args.vi < args.v_fmts.size() && !args.v_fmts[args.vi].empty()) {
      out += args.v_fmts[args.vi];
    }
    ++args.vi;
    i = j;
    return true;
  }

  if (spec == 'p' && args.vi < args.p_fmts.size() &&
      !args.p_fmts[args.vi].empty()) {
    out += args.p_fmts[args.vi];
    ++args.vi;
    i = j;
    return true;
  }
  if (args.vi < args.vals.size()) {
    if (spec == 't' && args.time_format != nullptr) {
      out += FormatTimeUnderTimeformat(args.vals[args.vi++],
                                       *args.time_format);
    } else {
      out += FormatArg(args.vals[args.vi++], spec);
    }
  }
  i = j;
  return true;
}

std::string FormatDisplay(const std::string& fmt,
                          const std::vector<Logic4Vec>& vals,
                          const std::vector<std::string>& p_fmts,
                          const TimeFormatSpec* time_format,
                          const std::vector<std::string>& v_fmts) {
  std::string out;
  FormatArgs args{vals, 0, p_fmts, time_format, v_fmts};
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

}
