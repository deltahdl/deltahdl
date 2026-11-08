#pragma once

#include <cstdint>
#include <string>
#include <string_view>

#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"

namespace delta {

inline constexpr std::string_view kDigestBlockKeyword = "digest_block";

struct ProtectDigestBlockPolicy {
  bool requested = false;
  std::string method;
  std::string stated_method;
  std::string key_method;
  std::string cipher;
  std::string keyname;
  std::string key;
};

std::string ProtectDigestBlockDirectives(std::string_view cleartext,
                                         const ProtectDigestBlockPolicy& policy,
                                         const ProtectEncoding& encoding);

struct ProtectDigestTarget {
  std::string cleartext;
  std::string key;
};

enum class ProtectDigestCheck : uint8_t {
  kNotChecked,
  kMatched,
  kAltered,
  kUnreadable,
};

ProtectDigestCheck CheckProtectDigestBlock(std::string_view block,
                                           const ProtectDigestTarget& target,
                                           std::string_view method,
                                           std::string_view cipher = {});

std::string_view ProtectDigestKeyByPublicKey(const ProtectKeywordScope& scope,
                                             const ProtectKeyList& keys);

}  // namespace delta
