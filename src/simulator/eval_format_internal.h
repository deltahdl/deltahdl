#pragma once

#include <cstdint>
#include <string>

#include "common/types.h"

namespace delta {

// Defined in eval_format_decimal.cpp. The decimal numeral of `val`, a known
// value of any width, read from every word it holds: negative, with a leading
// minus sign, where the value is signed and its top bit is set (§21.2.1.1).
std::string FormatDecimalDigits(const Logic4Vec& val);

// Defined in eval_format_decimal.cpp. §21.2.1.2: the number of columns the
// automatically sized decimal field of `val` occupies, enough for the largest
// value its width could hold, at any width.
uint32_t AutoDecimalFieldWidth(const Logic4Vec& val);

// §21.2.1.1: the optional field width and precision a format specification may
// carry -- "%10.3g" is a minimum field width of 10 with 3 fractional digits --
// and, for Table 21-2's real specifiers, C's flags (printed page 658). A width
// or precision that was not written is absent rather than zero, so the
// renderer can substitute "no minimum" and C's default of 6.
struct FormatFieldSpec {
  bool has_width = false;
  uint32_t width = 0;
  bool has_precision = false;
  uint32_t precision = 0;
  bool left_justify = false;
  bool plus_sign = false;
  bool space_sign = false;
  bool alternate = false;
  bool zero_pad = false;
  // %E, %F or %G: C's uppercase exponent letter, INF and NAN.
  bool uppercase = false;
};

// Defined in eval_format_real.cpp. `val` under the real specifier `spec` (e, f
// or g, or their uppercase forms) with no field width, precision or flag.
std::string FormatValueAsReal(const Logic4Vec& val, char spec);

// Defined in eval_format_real.cpp. `val` under the real specifier `spec` with
// the width, precision and flags `field` carries.
std::string FormatRealFormatted(const Logic4Vec& val, char spec,
                                const FormatFieldSpec& field);

// Defined in eval_format_real.cpp. A real value under %d: its integer part.
std::string FormatRealAsInt(const Logic4Vec& val);

}  // namespace delta
