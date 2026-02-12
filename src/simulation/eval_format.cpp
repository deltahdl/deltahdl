#include <cstdio>
#include <cstring>
#include <string>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"
#include "simulation/eval.h"

namespace delta {

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

std::string FormatArg(const Logic4Vec& val, char spec) {
  if (val.is_real && spec == 'd') return FormatRealAsInt(val);

  uint64_t v = val.ToUint64();
  char buf[64];
  switch (spec) {
    case 'd':
      return FormatDecimal(val);
    case 'h':
    case 'x': {
      // §21.2.1.2: %h prints ceil(width/4) hex digits with leading zeros.
      uint32_t ndigits = (val.width + 3) / 4;
      if (ndigits == 0) ndigits = 1;
      std::snprintf(buf, sizeof(buf), "%0*llx", static_cast<int>(ndigits),
                    static_cast<unsigned long long>(v));
      return buf;
    }
    case 'o': {
      // §21.2.1.2: %o prints ceil(width/3) octal digits with leading zeros.
      uint32_t ndigits = (val.width + 2) / 3;
      if (ndigits == 0) ndigits = 1;
      std::snprintf(buf, sizeof(buf), "%0*llo", static_cast<int>(ndigits),
                    static_cast<unsigned long long>(v));
      return buf;
    }
    case 'b':
      return val.ToString();
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
      return val.ToString();
  }
}

// Append a literal (non-format) character, handling backslash escapes.
static void AppendLiteralChar(const std::string& fmt, size_t& i,
                              std::string& out) {
  if (fmt[i] == '\\' && i + 1 < fmt.size()) {
    out += (fmt[i + 1] == 'n') ? '\n' : fmt[i + 1];
    ++i;
  } else {
    out += fmt[i];
  }
}

// Process a single format specifier starting at '%'.
// Advances i past the specifier and returns true if an arg was consumed.
static bool ProcessFormatSpec(const std::string& fmt, size_t& i,
                              const std::vector<Logic4Vec>& vals, size_t& vi,
                              std::string& out,
                              const std::vector<std::string>& p_fmts) {
  // Handle %m (hierarchical name -- no arg consumed).
  if (fmt[i + 1] == 'm') {
    out += "<module>";
    ++i;
    return false;
  }
  // Handle %% (literal percent).
  if (fmt[i + 1] == '%') {
    out += '%';
    ++i;
    return false;
  }
  // Skip optional '0' width modifier (e.g. %0d).
  size_t j = i + 1;
  while (j < fmt.size() && (fmt[j] >= '0' && fmt[j] <= '9')) ++j;
  char spec = (j < fmt.size()) ? fmt[j] : 'd';
  // §21.2.1.6: %p uses pre-computed assignment pattern format.
  if (spec == 'p' && vi < p_fmts.size() && !p_fmts[vi].empty()) {
    out += p_fmts[vi];
    ++vi;
    i = j;
    return true;
  }
  if (vi < vals.size()) {
    out += FormatArg(vals[vi++], spec);
  }
  i = j;
  return true;
}

std::string FormatDisplay(const std::string& fmt,
                          const std::vector<Logic4Vec>& vals,
                          const std::vector<std::string>& p_fmts) {
  std::string out;
  size_t vi = 0;
  for (size_t i = 0; i < fmt.size(); ++i) {
    if (fmt[i] != '%' || i + 1 >= fmt.size()) {
      AppendLiteralChar(fmt, i, out);
      continue;
    }
    ProcessFormatSpec(fmt, i, vals, vi, out, p_fmts);
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
