#pragma once

#include <cstdint>
#include <string>

#include "common/types.h"

namespace delta {

std::string FormatDecimalDigits(const Logic4Vec& val);

uint32_t AutoDecimalFieldWidth(const Logic4Vec& val);

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
  bool uppercase = false;
};

std::string FormatValueAsReal(const Logic4Vec& val, char spec);

std::string FormatRealFormatted(const Logic4Vec& val, char spec,
                                const FormatFieldSpec& field);

std::string FormatRealAsInt(const Logic4Vec& val);

}  // namespace delta
