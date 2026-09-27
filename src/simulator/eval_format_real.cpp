#include <cctype>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <string>

#include "common/types.h"
#include "simulator/eval_format_internal.h"
#include "simulator/evaluation.h"

namespace delta {

// §21.2.1.1 (printed page 658): Table 21-2's specifiers "are used with real
// numbers", so an integral operand is read for its value, converted as §6.12.1
// (printed 110) converts an expression assigned to a real -- "Individual bits
// that are x or z ... shall be treated as zero" -- and signed where the
// operand is. Read as a real's bit pattern, `$display("%f", 5)` printed
// 0.000000.
static double OperandAsReal(const Logic4Vec& val) {
  if (val.is_real) return RealVecToDouble(val);
  if (val.nwords == 0 || val.width == 0) return 0.0;
  uint64_t bits = val.words[0].aval & ~val.words[0].bval;
  if (val.width < 64) {
    uint64_t mask = (uint64_t{1} << val.width) - 1;
    bits &= mask;
    if (val.is_signed && ((bits >> (val.width - 1)) & 1U) != 0U) {
      return static_cast<double>(static_cast<int64_t>(bits | ~mask));
    }
  } else if (val.is_signed) {
    return static_cast<double>(static_cast<int64_t>(bits));
  }
  return static_cast<double>(bits);
}

std::string FormatValueAsReal(const Logic4Vec& val, char spec) {
  FormatFieldSpec field;
  field.uppercase = std::isupper(static_cast<unsigned char>(spec)) != 0;
  return FormatRealFormatted(
      val, static_cast<char>(std::tolower(static_cast<unsigned char>(spec))),
      field);
}

// The digits of `d` under the real specifier `spec` with `precision`
// fractional digits, C's alternate form when `alt`. Literal format strings
// keep each call clear of a runtime-built template.
static std::string RealDigits(double d, char spec, int precision, bool alt) {
  char buf[512];
  if (spec == 'e') {
    if (alt) {
      std::snprintf(buf, sizeof(buf), "%#.*e", precision, d);
    } else {
      std::snprintf(buf, sizeof(buf), "%.*e", precision, d);
    }
  } else if (spec == 'g') {
    if (alt) {
      std::snprintf(buf, sizeof(buf), "%#.*g", precision, d);
    } else {
      std::snprintf(buf, sizeof(buf), "%.*g", precision, d);
    }
  } else if (alt) {
    std::snprintf(buf, sizeof(buf), "%#.*f", precision, d);
  } else {
    std::snprintf(buf, sizeof(buf), "%.*f", precision, d);
  }
  return buf;
}

// Table 21-2's "%e or %E" and the rest: the uppercase form writes C's
// uppercase exponent letter, INF and NAN, the digits being the same. C's `+`
// signs a non-negative value and its space puts a blank where the sign would
// be.
static void CaseAndSignDigits(std::string& text, const FormatFieldSpec& field) {
  if (field.uppercase) {
    for (char& c : text) {
      c = static_cast<char>(std::toupper(static_cast<unsigned char>(c)));
    }
  }
  if (text.empty() || text.front() == '-') return;
  if (field.plus_sign) {
    text.insert(0, 1, '+');
  } else if (field.space_sign) {
    text.insert(0, 1, ' ');
  }
}

// §21.2.1.1 (printed page 658): Table 21-2's real specifiers "have the full
// formatting capabilities available in the C language" -- "%10.3g" is a
// minimum field width of 10 with 3 fractional digits, and C's flags apply as
// C applies them: `-` left-justifies in the field, `+` signs a non-negative
// value and a space puts a blank where its sign would be, `#` keeps the
// decimal point, and a field width written with a leading 0 pads with zeros
// after the sign; %E, %F and %G write their letters uppercase. A precision not
// written is C's default of 6.
std::string FormatRealFormatted(const Logic4Vec& val, char spec,
                                const FormatFieldSpec& field) {
  double d = OperandAsReal(val);
  int precision = field.has_precision ? static_cast<int>(field.precision) : 6;
  std::string text = RealDigits(d, spec, precision, field.alternate);
  CaseAndSignDigits(text, field);
  size_t width = field.has_width ? field.width : 0;
  if (text.size() >= width) return text;
  size_t pad = width - text.size();
  if (field.left_justify) {
    text.append(pad, ' ');
  } else if (field.zero_pad && std::isfinite(d)) {
    bool signed_text =
        text.front() == '-' || text.front() == '+' || text.front() == ' ';
    text.insert(signed_text ? 1 : 0, pad, '0');
  } else {
    text.insert(0, pad, ' ');
  }
  return text;
}

std::string FormatRealAsInt(const Logic4Vec& val) {
  double d = RealVecToDouble(val);
  char buf[64];
  std::snprintf(buf, sizeof(buf), "%lld", static_cast<long long>(d));
  return buf;
}

}  // namespace delta
