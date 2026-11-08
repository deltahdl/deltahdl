#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "simulator/eval_format_internal.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/scope_hier_name.h"
#include "simulator/sim_context.h"

namespace delta {

struct FormatArgs {
  const std::vector<Logic4Vec>& vals;
  size_t vi = 0;
  const std::vector<std::string>& p_fmts;
  const TimeFormatSpec* time_format = nullptr;
  const std::vector<std::string>& v_fmts;
  const std::vector<char>& nonscalar_nets;
  SimContext* ctx = nullptr;
  const std::vector<char>& agg_flags;
  const std::vector<std::string>& s_fmts;
  SourceLoc loc;
};

static std::string BuildInstanceBinding(SimContext* ctx) {
  if (ctx != nullptr) {
    const Process* proc = ctx->CurrentProcess();
    std::string prefix;
    if (proc != nullptr && !proc->caller_inst_prefixes.empty()) {
      prefix = proc->inst_prefix;
    } else if (ctx->DeferredBindingScope().has_value()) {
      prefix = *ctx->DeferredBindingScope();
    } else {
      prefix = ctx->ActiveInstancePrefix();
    }
    if (!prefix.empty() && prefix.back() == '.') prefix.pop_back();
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
    if (ch == 0 && result.empty()) continue;
    result += ch;
  }
  return result;
}

static std::string FormatDecimal(const Logic4Vec& val) {
  return FormatDecimalDigits(val);
}

enum class XZClass : std::uint8_t { kKnown, kAllX, kAllZ, kSomeX, kSomeZ };

static void ReadBit(const Logic4Vec& val, uint32_t i, bool& a, bool& b) {
  uint32_t w = i / 64;
  uint64_t mask = uint64_t{1} << (i % 64);
  a = (val.words[w].aval & mask) != 0;
  b = (val.words[w].bval & mask) != 0;
}

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

static std::string FormatDecimalXZ(const Logic4Vec& val) {
  char xz = XZDigitChar(ClassifyBits(val, 0, val.width));
  if (xz != 0) return std::string(1, xz);
  return FormatDecimal(val);
}

static std::string FormatDecimalAutoSized(const Logic4Vec& val) {
  std::string core = FormatDecimalXZ(val);
  uint32_t field = AutoDecimalFieldWidth(val);
  if (core.size() >= field) return core;
  return std::string(field - core.size(), ' ') + core;
}

static uint32_t ChunkMask(uint32_t width, uint32_t off) {
  uint32_t valid = (width > off) ? (width - off) : 0;
  if (valid >= 32) return 0xFFFFFFFFu;
  return (uint32_t{1} << valid) - 1;
}

static std::string FormatUnformatted2Value(const Logic4Vec& val) {
  std::string out;
  uint32_t nchunks = (val.width + 31) / 32;
  if (nchunks == 0) nchunks = 1;
  for (uint32_t k = 0; k < nchunks; ++k) {
    uint32_t off = k * 32;
    uint32_t w = off / 64;
    uint64_t aval = (w < val.nwords) ? val.words[w].aval : 0;
    uint64_t bval = (w < val.nwords) ? val.words[w].bval : 0;
    auto two = static_cast<uint32_t>((aval & ~bval) >> (off % 64));
    two &= ChunkMask(val.width, off);
    for (int b = 0; b < 4; ++b)
      out += static_cast<char>((two >> (b * 8)) & 0xFF);
  }
  return out;
}

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

std::string FormatTimeUnderTimeformat(const Logic4Vec& val,
                                      const TimeFormatSpec& spec,
                                      int value_order) {
  long double time = 0;
  if (val.is_real) {
    double d = 0;
    uint64_t bits = val.ToUint64();
    std::memcpy(&d, &bits, sizeof(d));
    time = d;
  } else {
    time = static_cast<long double>(val.ToUint64());
  }
  time *= std::pow(10.0L, value_order - spec.units_number);
  char buf[64];
  std::snprintf(buf, sizeof(buf), "%.*Lf", spec.precision_number, time);
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
  char written = spec;
  if (spec >= 'A' && spec <= 'Z') spec = static_cast<char>(spec - 'A' + 'a');

  if (val.is_real && spec == 'd') return FormatRealAsInt(val);

  uint64_t v = val.ToUint64();
  char buf[64];
  switch (spec) {
    case 'd':
      return FormatDecimalXZ(val);
    case 'h':
    case 'x':
      return FormatRadixXZ(val, 4);
    case 'o':
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
      return FormatUnformatted2Value(val);
    case 'z':
      return FormatUnformatted4Value(val);
    case 'e':
    case 'f':
    case 'g':
      return FormatValueAsReal(val, written);
    default:
      std::fprintf(stderr, "[deltahdl] unknown format specifier: %%%c\n", spec);
      return std::string("%") + spec;
  }
}

static const char* StrengthMnemonic(uint8_t level) {
  static const char* k_mnemonics[8] = {"Hi", "Sm", "Me", "We",
                                       "La", "Pu", "St", "Su"};
  return k_mnemonics[level & 0x7];
}

std::string FormatStrength(const NetStrength& ns) {
  auto s0_hi = static_cast<uint8_t>(ns.s0_hi);
  auto s0_lo = static_cast<uint8_t>(ns.s0_lo);
  auto s1_hi = static_cast<uint8_t>(ns.s1_hi);
  auto s1_lo = static_cast<uint8_t>(ns.s1_lo);

  bool drives0 = s0_hi != 0;
  bool drives1 = s1_hi != 0;

  if (!drives0 && !drives1) return "HiZ";

  if (drives0 && drives1) {
    if (s0_hi == s1_hi) return std::string(StrengthMnemonic(s0_hi)) + "X";
    return std::string(1, static_cast<char>('0' + s0_hi)) +
           static_cast<char>('0' + s1_hi) + "X";
  }

  uint8_t hi = drives0 ? s0_hi : s1_hi;
  uint8_t lo = drives0 ? s0_lo : s1_lo;
  char known = drives0 ? '0' : '1';

  if (lo == 0) {
    char ambiguous = drives0 ? 'L' : 'H';
    return std::string(StrengthMnemonic(hi)) + ambiguous;
  }

  if (hi == lo) return std::string(StrengthMnemonic(hi)) + known;
  return std::string(1, static_cast<char>('0' + hi)) +
         static_cast<char>('0' + lo) + known;
}

static std::string TrimLeadingZeros(const std::string& full) {
  size_t start = full.find_first_not_of('0');
  if (start == std::string::npos) return "0";
  return full.substr(start);
}

static std::string FormatRadixMinimal(const Logic4Vec& val,
                                      uint32_t bits_per_digit) {
  std::string full = FormatRadixXZ(val, bits_per_digit);
  return val.IsKnown() ? TrimLeadingZeros(full) : full;
}

static std::string FormatArgMinimal(const Logic4Vec& val, char spec) {
  switch (spec) {
    case 'h':
    case 'x':
      return FormatRadixMinimal(val, 4);
    case 'o':
      return FormatRadixMinimal(val, 3);
    case 'b':
      return TrimLeadingZeros(val.ToString());
    default:
      return FormatArg(val, spec);
  }
}

static std::string FormatArgWidth(const Logic4Vec& val, char spec,
                                  bool has_width, uint32_t width) {
  if (!has_width) return FormatArgAutoSized(val, spec);

  char norm = spec;
  if (norm >= 'A' && norm <= 'Z') norm = static_cast<char>(norm - 'A' + 'a');

  if (norm == 'e' || norm == 'f' || norm == 'g' || norm == 't')
    return FormatArg(val, spec);

  std::string core = FormatArgMinimal(val, norm);
  if (width == 0 || core.size() >= width) return core;

  char pad =
      (norm == 'h' || norm == 'x' || norm == 'o' || norm == 'b') ? '0' : ' ';
  return std::string(width - core.size(), pad) + core;
}

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

static char FormatNamedEscape(char c) {
  switch (c) {
    case 'n':
      return '\n';
    case 't':
      return '\t';
    case '\\':
      return '\\';
    case '"':
      return '"';
    case 'v':
      return '\v';
    case 'f':
      return '\f';
    case 'a':
      return '\a';
    default:
      return 0;
  }
}

static bool TryAppendNumericEscape(const std::string& fmt, size_t& i, char c,
                                   std::string& out) {
  if (c == 'x') {
    int val = 0;
    for (int j = 0;
         j < 2 && i + 1 < fmt.size() && FormatHexDigitVal(fmt[i + 1]) >= 0; ++j)
      val = val * 16 + FormatHexDigitVal(fmt[++i]);
    out += static_cast<char>(val);
    return true;
  }
  if (c >= '0' && c <= '7') {
    int val = c - '0';
    for (int j = 0;
         j < 2 && i + 1 < fmt.size() && fmt[i + 1] >= '0' && fmt[i + 1] <= '7';
         ++j)
      val = val * 8 + (fmt[++i] - '0');
    out += static_cast<char>(val);
    return true;
  }
  return false;
}

static void AppendLiteralChar(const std::string& fmt, size_t& i,
                              std::string& out) {
  if (fmt[i] != '\\' || i + 1 >= fmt.size()) {
    out += fmt[i];
    return;
  }
  char c = fmt[++i];
  if (c == '\n') return;
  if (c == '\r') {
    if (i + 1 < fmt.size() && fmt[i + 1] == '\n') ++i;
    return;
  }
  if (char named = FormatNamedEscape(c); named != 0) {
    out += named;
    return;
  }
  if (TryAppendNumericEscape(fmt, i, c, out)) return;
  out += c;
}

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

static bool IsRealSpec(char spec) {
  return spec == 'e' || spec == 'f' || spec == 'g';
}

static bool RecordCFlag(char c, FormatFieldSpec& flags) {
  switch (c) {
    case '-':
      flags.left_justify = true;
      return true;
    case '+':
      flags.plus_sign = true;
      return true;
    case ' ':
      flags.space_sign = true;
      return true;
    case '#':
      flags.alternate = true;
      return true;
    default:
      return false;
  }
}

static void ParseRealFlags(const std::string& fmt, size_t& start,
                           FormatFieldSpec& field) {
  size_t j = start;
  FormatFieldSpec flags;
  while (j < fmt.size() && RecordCFlag(fmt[j], flags)) ++j;
  if (j == start) return;
  size_t k = j;
  while (k < fmt.size() && ((fmt[k] >= '0' && fmt[k] <= '9') || fmt[k] == '.'))
    ++k;
  if (k >= fmt.size()) return;
  char spec = fmt[k];
  if (spec >= 'A' && spec <= 'Z') spec = static_cast<char>(spec - 'A' + 'a');
  if (!IsRealSpec(spec)) return;
  field = flags;
  start = j;
}

static bool TryNoArgScopeSpec(char spec, FormatArgs& args, std::string& out) {
  if (spec == 'm') {
    if (args.ctx != nullptr) out += ScopeHierName(*args.ctx);
    return true;
  }
  if (spec == 'l') {
    out += BuildInstanceBinding(args.ctx);
    return true;
  }
  return false;
}

static const char* NonScalarPercentVReport(char nonscalar) {
  if (nonscalar == 2) {
    return "a %v format specification takes a scalar reference, and the "
           "argument it consumed is a select naming more than one bit of a net";
  }
  return "a %v format specification takes a scalar reference, and the argument "
         "it consumed is a net declared with a range";
}

static void AppendStrengthArg(FormatArgs& args, std::string& out) {
  char nonscalar =
      args.vi < args.nonscalar_nets.size() ? args.nonscalar_nets[args.vi] : 0;
  if (nonscalar != 0) {
    if (args.ctx != nullptr) {
      args.ctx->GetDiag().Error(args.loc, NonScalarPercentVReport(nonscalar),
                                Subclause("21.2.1.4"));
    }
  } else if (args.vi < args.v_fmts.size() && !args.v_fmts[args.vi].empty()) {
    out += args.v_fmts[args.vi];
  }
  ++args.vi;
}

static bool TryPrecomputedArgSpec(char spec, FormatArgs& args,
                                  std::string& out) {
  if (spec == 'v') {
    AppendStrengthArg(args, out);
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

static char NormalizeFormatSpec(char spec) {
  if (spec >= 'A' && spec <= 'Z') return static_cast<char>(spec - 'A' + 'a');
  return spec;
}

static bool RejectIntegerSpecOnAggregate(char norm, FormatArgs& args) {
  bool is_integer_spec = norm == 'd' || norm == 'h' || norm == 'x' ||
                         norm == 'o' || norm == 'b' || norm == 'c' ||
                         norm == 'u' || norm == 'z';
  if (!is_integer_spec || args.vi >= args.agg_flags.size() ||
      args.agg_flags[args.vi] == 0)
    return false;
  if (args.agg_flags[args.vi] == 3 && (norm == 'u' || norm == 'z'))
    return false;
  if (args.ctx != nullptr) {
    args.ctx->GetDiag().Error(
        args.loc,
        "an integer format specifier cannot be applied to an unpacked "
        "aggregate argument",
        Subclause("21.2.1.1"));
  }
  ++args.vi;
  return true;
}

static bool AppendStringSpecOnAggregate(char norm, FormatArgs& args,
                                        std::string& out) {
  if (norm != 's' || args.vi >= args.agg_flags.size() ||
      args.agg_flags[args.vi] == 0 || args.agg_flags[args.vi] == 3)
    return false;
  if (args.agg_flags[args.vi] == 2 && args.vi < args.s_fmts.size()) {
    out += args.s_fmts[args.vi];
  } else if (args.ctx != nullptr) {
    args.ctx->GetDiag().Error(
        args.loc,
        "a string format specifier applied to an unpacked array requires "
        "elements of type byte",
        Subclause("21.2.1.7"));
  }
  ++args.vi;
  return true;
}

static void AppendRenderedValue(char spec, char norm,
                                const FormatFieldSpec& field, FormatArgs& args,
                                std::string& out) {
  const TimeFormatSpec* tf = args.time_format;
  if (tf == nullptr && args.ctx != nullptr) tf = &args.ctx->GetTimeFormat();
  if (spec == 't' && tf != nullptr) {
    TimeFormatSpec widened = *tf;
    if (field.has_width) {
      widened.minimum_field_width = static_cast<int>(field.width);
    }
    int value_order = widened.units_number;
    if (args.ctx != nullptr) {
      const TimeScale& scale = ActiveInstanceTimeScale(*args.ctx);
      value_order = EffectiveTimeOrder(scale.unit, scale.magnitude);
    }
    out +=
        FormatTimeUnderTimeformat(args.vals[args.vi++], widened, value_order);
    return;
  }
  if (IsRealSpec(norm) &&
      (field.has_width || field.has_precision || field.left_justify ||
       field.plus_sign || field.space_sign || field.alternate ||
       field.uppercase)) {
    out += FormatRealFormatted(args.vals[args.vi++], norm, field);
    return;
  }
  out +=
      FormatArgWidth(args.vals[args.vi++], spec, field.has_width, field.width);
}

static void AppendValueArg(char spec, const FormatFieldSpec& field,
                           FormatArgs& args, std::string& out) {
  if (args.vi >= args.vals.size()) return;
  char norm = NormalizeFormatSpec(spec);
  if (RejectIntegerSpecOnAggregate(norm, args)) return;
  if (AppendStringSpecOnAggregate(norm, args, out)) return;
  AppendRenderedValue(spec, norm, field, args, out);
}

static bool ProcessFormatSpec(const std::string& fmt, size_t& i,
                              FormatArgs& args, std::string& out) {
  if (fmt[i + 1] == '%') {
    out += '%';
    ++i;
    return false;
  }

  size_t j = i + 1;
  FormatFieldSpec field;
  ParseRealFlags(fmt, j, field);
  bool has_width = false;
  uint32_t width = 0;
  field.zero_pad = field.zero_pad || (j + 1 < fmt.size() && fmt[j] == '0' &&
                                      fmt[j + 1] >= '1' && fmt[j + 1] <= '9');
  ParseFieldWidth(fmt, j, has_width, width);

  bool has_prec = false;
  uint32_t prec = 0;
  if (j < fmt.size() && fmt[j] == '.') {
    ++j;
    ParseFieldWidth(fmt, j, has_prec, prec);
    has_prec = true;
  }

  char spec = (j < fmt.size()) ? fmt[j] : 'd';

  field.uppercase = spec == 'E' || spec == 'F' || spec == 'G';
  if (spec >= 'A' && spec <= 'Z') spec = static_cast<char>(spec - 'A' + 'a');

  if (TryNoArgScopeSpec(spec, args, out)) {
    i = j;
    return false;
  }

  if (TryPrecomputedArgSpec(spec, args, out)) {
    i = j;
    return true;
  }

  field.has_width = has_width;
  field.width = width;
  field.has_precision = has_prec;
  field.precision = prec;
  if (!IsRealSpec(spec)) field.zero_pad = false;
  AppendValueArg(spec, field, args, out);
  i = j;
  return true;
}

std::string FormatDisplay(const std::string& fmt,
                          const std::vector<Logic4Vec>& vals,
                          const DisplayFormatOpts& opts) {
  std::string out;
  static const std::vector<std::string> kEmpty;
  static const std::vector<char> kEmptyFlags;
  const std::vector<std::string>& p_fmts =
      opts.p_fmts != nullptr ? *opts.p_fmts : kEmpty;
  const std::vector<std::string>& v_fmts =
      opts.v_fmts != nullptr ? *opts.v_fmts : kEmpty;
  const std::vector<char>& nonscalar_nets =
      opts.arg_nonscalar_net != nullptr ? *opts.arg_nonscalar_net : kEmptyFlags;
  const std::vector<char>& agg_flags =
      opts.arg_unpacked_agg != nullptr ? *opts.arg_unpacked_agg : kEmptyFlags;
  const std::vector<std::string>& s_fmts =
      opts.arg_byte_strings != nullptr ? *opts.arg_byte_strings : kEmpty;
  FormatArgs args{
      vals,           0,        p_fmts,    opts.time_format, v_fmts,
      nonscalar_nets, opts.ctx, agg_flags, s_fmts,           opts.loc};
  for (size_t i = 0; i < fmt.size(); ++i) {
    if (fmt[i] != '%' || i + 1 >= fmt.size()) {
      AppendLiteralChar(fmt, i, out);
      continue;
    }
    ProcessFormatSpec(fmt, i, args, out);
  }
  return out;
}

}  // namespace delta
