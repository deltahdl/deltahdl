#include <cstdint>
#include <cstdio>
#include <cstring>
#include <string>
#include <vector>

#include "common/diagnostic.h"
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
  // §21.2.1.1 / §21.2.1.7: per-argument aggregate classification. 0 means the
  // argument is not an unpacked aggregate; 1 means it is one whose elements
  // are not of type byte (an integer format specifier consuming it is
  // rejected, and %s rejects it too); 2 means it is an unpacked array of
  // byte, which %s renders through the precomputed string below.
  const std::vector<char>& agg_flags;
  // §21.2.1.7: per-argument character rendering of an unpacked array of byte,
  // elements taken from the left bound to the right bound. Precomputed by the
  // calling task, which holds the element variables; empty for any argument
  // that is not such an array.
  const std::vector<std::string>& s_fmts;
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
    // §21.2.1.7: the value is read as 8-bit groups, high group first, and
    // leading zeros are never printed. Only the zeros ahead of the first
    // nonzero group are "leading"; a zero byte that follows a printed
    // character is part of the value and passes through. No termination
    // character is appended.
    if (ch == 0 && result.empty()) continue;
    result += ch;
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

// §21.2.1.1: Table 21-2 real specifiers carry the full C-language field-width
// and precision capability -- e.g. "%10.3g" is a minimum field width of 10 with
// 3 fractional digits. Reconstruct the double and render it with the parsed
// width/precision. A width of zero means "no minimum" and, when no precision
// was written, the C default of 6 is used, matching the plain %e/%f/%g
// rendering.
static std::string FormatRealFormatted(const Logic4Vec& val, char spec,
                                       bool has_width, uint32_t width,
                                       bool has_prec, uint32_t prec) {
  uint64_t bits = val.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &bits, sizeof(double));
  int w = has_width ? static_cast<int>(width) : 0;
  int p = has_prec ? static_cast<int>(prec) : 6;
  char buf[256];
  // Literal format strings with variadic '*' width/precision keep the call
  // clear of a runtime-built format template.
  if (spec == 'e') {
    std::snprintf(buf, sizeof(buf), "%*.*e", w, p, d);
  } else if (spec == 'g') {
    std::snprintf(buf, sizeof(buf), "%*.*g", w, p, d);
  } else {
    std::snprintf(buf, sizeof(buf), "%*.*f", w, p, d);
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

// §21.2.1.2: the number of columns the automatically sized decimal field
// occupies -- enough characters for the largest value the expression could
// possibly hold. An unsigned width-w value tops out at 2^w - 1; a signed one
// is bounded in print length by its most negative value, whose magnitude
// 2^(w-1) is joined by a sign column. Rendering reads at most 64 bits, so a
// wider value sizes as a 64-bit one.
static uint32_t AutoDecimalFieldWidth(const Logic4Vec& val) {
  uint32_t bits = val.width;
  if (bits == 0) bits = 1;
  if (bits > 64) bits = 64;
  uint64_t max_mag;
  if (val.is_signed) {
    max_mag = uint64_t{1} << (bits - 1);
  } else {
    max_mag = (bits == 64) ? ~uint64_t{0} : (uint64_t{1} << bits) - 1;
  }
  uint32_t digits = 1;
  while (max_mag >= 10) {
    max_mag /= 10;
    ++digits;
  }
  return digits + (val.is_signed ? 1u : 0u);
}

// §21.2.1.2: the automatically sized decimal rendering. Suppressed leading
// zeros are replaced by spaces, so the numeral sits right-justified in the
// fixed-width field computed above; a §21.2.1.3 status character occupies the
// same field. A converted result at or beyond the field width is emitted
// whole -- never truncated.
static std::string FormatDecimalAutoSized(const Logic4Vec& val) {
  std::string core = FormatDecimalXZ(val);
  uint32_t field = AutoDecimalFieldWidth(val);
  if (core.size() >= field) return core;
  return std::string(field - core.size(), ' ') + core;
}

// §21.2.1.1: mask for the valid low bits of the top 32-bit chunk of a value.
// Bits at and above `width` are not part of the value; the fully populated
// chunks below the top return an all-ones mask.
static uint32_t ChunkMask(uint32_t width, uint32_t off) {
  uint32_t valid = (width > off) ? (width - off) : 0;
  if (valid >= 32) return 0xFFFFFFFFu;
  return (uint32_t{1} << valid) - 1;
}

// §21.2.1.1: %u writes the value as raw, unformatted 2-value binary. Any
// unknown (x) or high-impedance (z) bit shall be emitted as zero, so the
// 2-value word is the aval bits with every bval-marked bit cleared. The value
// is packed into 32-bit words, the word holding the LSB written first, each
// word laid down in the machine's native (little-endian) byte order.
static std::string FormatUnformatted2Value(const Logic4Vec& val) {
  std::string out;
  uint32_t nchunks = (val.width + 31) / 32;
  if (nchunks == 0) nchunks = 1;
  for (uint32_t k = 0; k < nchunks; ++k) {
    uint32_t off = k * 32;
    uint32_t w = off / 64;
    uint64_t aval = (w < val.nwords) ? val.words[w].aval : 0;
    uint64_t bval = (w < val.nwords) ? val.words[w].bval : 0;
    uint32_t two = static_cast<uint32_t>((aval & ~bval) >> (off % 64));
    two &= ChunkMask(val.width, off);
    for (int b = 0; b < 4; ++b)
      out += static_cast<char>((two >> (b * 8)) & 0xFF);
  }
  return out;
}

// §21.2.1.1: %z writes the value as raw, unformatted 4-value binary, preserving
// x and z. Each 32-bit chunk is emitted as the (aval, bval) pair of the
// s_vpi_vecval layout (Figure 38-8), whose per-bit encoding already matches
// Logic4Vec's (a known bit clears bval; x is aval&bval, z is bval alone). The
// chunk holding the LSB is written first, each 32-bit word native-endian.
static std::string FormatUnformatted4Value(const Logic4Vec& val) {
  std::string out;
  uint32_t nchunks = (val.width + 31) / 32;
  if (nchunks == 0) nchunks = 1;
  auto emit32 = [&out](uint32_t x) {
    for (int b = 0; b < 4; ++b) out += static_cast<char>((x >> (b * 8)) & 0xFF);
  };
  for (uint32_t k = 0; k < nchunks; ++k) {
    uint32_t off = k * 32;
    uint32_t w = off / 64;
    uint64_t aval = (w < val.nwords) ? val.words[w].aval : 0;
    uint64_t bval = (w < val.nwords) ? val.words[w].bval : 0;
    uint32_t mask = ChunkMask(val.width, off);
    emit32(static_cast<uint32_t>(aval >> (off % 64)) & mask);
    emit32(static_cast<uint32_t>(bval >> (off % 64)) & mask);
  }
  return out;
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
    case 'u':
      // §21.2.1.1: unformatted 2-value binary; x/z bits become zero.
      return FormatUnformatted2Value(val);
    case 'z':
      // §21.2.1.1: unformatted 4-value binary; x and z are preserved.
      return FormatUnformatted4Value(val);
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
  if (!has_width) return FormatArgAutoSized(val, spec);

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

// §21.2.1.2: automatic sizing of a displayed expression argument, applied when
// no explicit field width overrides it -- both to a format-specifier argument
// and to a bare argument rendered under a task's default radix (§21.2.1.1).
// Decimal takes the fixed-width, space-filled field above; the other radices'
// plain renderings (full bit width, leading zeros kept) are already
// automatically sized, as are the real, string, and time forms. A real value
// under %d has no bit-width to size against and keeps its plain rendering.
std::string FormatArgAutoSized(const Logic4Vec& val, char spec) {
  char norm = spec;
  if (norm >= 'A' && norm <= 'Z') norm = static_cast<char>(norm - 'A' + 'a');
  if (norm == 'd' && !val.is_real) return FormatDecimalAutoSized(val);
  return FormatArg(val, spec);
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
                           bool has_prec, uint32_t prec, FormatArgs& args,
                           std::string& out) {
  if (args.vi < args.vals.size()) {
    char norm = spec;
    if (norm >= 'A' && norm <= 'Z') norm = static_cast<char>(norm - 'A' + 'a');

    // §21.2.1.1: the integer format specifiers may not be applied to an
    // unpacked aggregate argument. When the caller flagged this positional
    // argument as one, reject it and render nothing rather than emitting a
    // bogus value.
    bool is_integer_spec = norm == 'd' || norm == 'h' || norm == 'x' ||
                           norm == 'o' || norm == 'b' || norm == 'c' ||
                           norm == 'u' || norm == 'z';
    if (is_integer_spec && args.vi < args.agg_flags.size() &&
        args.agg_flags[args.vi] != 0) {
      if (args.ctx != nullptr) {
        args.ctx->GetDiag().Error(
            {},
            "an integer format specifier cannot be applied to an unpacked "
            "aggregate argument");
      }
      ++args.vi;  // the argument is consumed even though nothing is rendered
      return;
    }

    // §21.2.1.7: the string specifier admits, besides an integral or
    // string-typed value, an unpacked array of byte -- rendered as the
    // characters its elements spell from the left bound to the right bound
    // (precomputed by the calling task). Any other unpacked aggregate has no
    // character rendering and is rejected.
    if (norm == 's' && args.vi < args.agg_flags.size() &&
        args.agg_flags[args.vi] != 0) {
      if (args.agg_flags[args.vi] == 2 && args.vi < args.s_fmts.size()) {
        out += args.s_fmts[args.vi];
      } else if (args.ctx != nullptr) {
        args.ctx->GetDiag().Error(
            {},
            "a string format specifier applied to an unpacked array requires "
            "elements of type byte");
      }
      ++args.vi;  // one argument is consumed either way
      return;
    }

    // §20.4.3: %t renders time through the active $timeformat configuration.
    // An explicitly threaded spec wins; otherwise the run-time context supplies
    // the configuration installed by the most recent $timeformat call (or the
    // Table 20-3 defaults when none has run yet). This is what makes a plain
    // $display/$fmonitor with %t honor $timeformat "for all %t formats in the
    // design until another $timeformat system task is invoked".
    const TimeFormatSpec* tf = args.time_format;
    if (tf == nullptr && args.ctx != nullptr) tf = &args.ctx->GetTimeFormat();
    if (spec == 't' && tf != nullptr) {
      out += FormatTimeUnderTimeformat(args.vals[args.vi++], *tf);
    } else if ((norm == 'e' || norm == 'f' || norm == 'g') &&
               (has_width || has_prec)) {
      // §21.2.1.1: the C-style width.precision (e.g. %10.3g) applies to reals.
      out += FormatRealFormatted(args.vals[args.vi++], norm, has_width, width,
                                 has_prec, prec);
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

  // §21.2.1.1: a real specifier may carry a C-style ".precision" after the
  // optional field width (e.g. "%10.3g"). Consume it here so the fractional-
  // digit count reaches the real renderer and never leaks into the output as
  // literal text. A lone '.' selects a precision of zero, as in C.
  bool has_prec = false;
  uint32_t prec = 0;
  if (j < fmt.size() && fmt[j] == '.') {
    ++j;
    ParseFieldWidth(fmt, j, has_prec, prec);
    has_prec = true;  // a lone '.' still means precision, defaulting to zero
  }

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

  AppendValueArg(spec, has_width, width, has_prec, prec, args, out);
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
  static const std::vector<char> kEmptyFlags;
  const std::vector<std::string>& p_fmts =
      opts.p_fmts != nullptr ? *opts.p_fmts : kEmpty;
  const std::vector<std::string>& v_fmts =
      opts.v_fmts != nullptr ? *opts.v_fmts : kEmpty;
  const std::vector<char>& agg_flags =
      opts.arg_unpacked_agg != nullptr ? *opts.arg_unpacked_agg : kEmptyFlags;
  const std::vector<std::string>& s_fmts =
      opts.arg_byte_strings != nullptr ? *opts.arg_byte_strings : kEmpty;
  FormatArgs args{vals,   0,        p_fmts,    opts.time_format,
                  v_fmts, opts.ctx, agg_flags, s_fmts};
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
