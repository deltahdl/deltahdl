#pragma once

#include <string>
#include <string_view>

#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"

namespace delta {

inline constexpr std::string_view kDigestKeyMethodKeyword = "digest_key_method";

inline constexpr std::string_view kDigestDecryptKeyKeyword =
    "digest_decrypt_key";

bool IsProtectDigestKeyMethodIdentifier(std::string_view identifier);

ProtectKeywordValue ProtectDigestKeyMethodInEffect(
    const ProtectKeywordScope& scope);

std::string ProtectDigestKeyMethodDirective(std::string_view method);

std::string ProtectDigestDecryptKeyDirective(std::string_view encoded_key);

struct ProtectDigestDecryption {
  std::string decrypt_key;
  std::string key_method;
  std::string keyname;
  std::string digest_method;
};

std::string ProtectDigestDecryptionContent(
    const ProtectDigestDecryption& digest, const ProtectEncoding& encoding);

}  // namespace delta
