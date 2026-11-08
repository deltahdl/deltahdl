#pragma once

#include <span>
#include <string>
#include <string_view>

#include "preprocessor/protect_keywords.h"

namespace delta {

inline constexpr std::string_view kDigestMethodKeyword = "digest_method";

inline constexpr std::string_view kSha1DigestMethod = "sha1";
inline constexpr std::string_view kMd5DigestMethod = "md5";
inline constexpr std::string_view kMd2DigestMethod = "md2";
inline constexpr std::string_view kRipemd160DigestMethod = "ripemd-160";

struct ProtectDigestAlgorithm {
  std::string_view identifier;
  bool required;
  std::string_view algorithm;
};

std::span<const ProtectDigestAlgorithm> ProtectDigestAlgorithms();

bool IsProtectDigestAlgorithm(std::string_view identifier);

bool IsRequiredProtectDigestAlgorithm(std::string_view identifier);

bool ProtectDigestIsAvailable(std::string_view identifier);

inline constexpr std::string_view kDefaultDigestMethod = kSha1DigestMethod;

ProtectKeywordValue ProtectDigestMethodInEffect(
    const ProtectKeywordScope& scope);

bool ProtectMessageDigest(std::string_view data, std::string_view identifier,
                          std::string* digest);

}  // namespace delta
