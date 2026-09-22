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

}  // namespace delta
