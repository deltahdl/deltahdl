#pragma once

#include <span>
#include <string_view>

#include "preprocessor/protect_keywords.h"

namespace delta {

inline constexpr std::string_view kKeyMethodKeyword = "key_method";

inline constexpr std::string_view kDesCbcMethod = "des-cbc";

struct ProtectEncryptionAlgorithm {
  std::string_view identifier;
  bool required;
  std::string_view algorithm;
};

std::span<const ProtectEncryptionAlgorithm> ProtectEncryptionAlgorithms();

bool IsProtectKeyMethodIdentifier(std::string_view identifier);

bool IsRequiredProtectEncryptionAlgorithm(std::string_view identifier);

ProtectKeywordValue ProtectKeyMethodInEffect(const ProtectKeywordScope& scope);

}  // namespace delta
