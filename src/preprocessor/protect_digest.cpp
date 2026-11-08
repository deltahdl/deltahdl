#include "preprocessor/protect_digest.h"

#include <span>
#include <string>
#include <string_view>

#include "preprocessor/protect_digest_algorithms.h"
#include "preprocessor/protect_keywords.h"

namespace delta {
namespace {

constexpr ProtectDigestAlgorithm kProtectDigestAlgorithms[] = {
    {kSha1DigestMethod, true, "Secure Hash Algorithm 1, see FIPS 180-2"},
    {kMd5DigestMethod, true, "Message Digest Algorithm 5, see IETF RFC 1321"},
    {kMd2DigestMethod, false, "Message Digest Algorithm 2, see IETF RFC 1319"},
    {kRipemd160DigestMethod, false, "RIPEMD-160, see ISO/IEC 10118-3:2004"},
};

const ProtectDigestAlgorithm* RowOfDigestTable(std::string_view identifier) {
  for (const ProtectDigestAlgorithm& row : kProtectDigestAlgorithms) {
    if (row.identifier == identifier) return &row;
  }
  return nullptr;
}

}  // namespace

std::span<const ProtectDigestAlgorithm> ProtectDigestAlgorithms() {
  return kProtectDigestAlgorithms;
}

bool IsProtectDigestAlgorithm(std::string_view identifier) {
  return RowOfDigestTable(identifier) != nullptr;
}

bool IsRequiredProtectDigestAlgorithm(std::string_view identifier) {
  const ProtectDigestAlgorithm* row = RowOfDigestTable(identifier);
  return row != nullptr && row->required;
}

bool ProtectDigestIsAvailable(std::string_view identifier) {
  return IsRequiredProtectDigestAlgorithm(identifier);
}

ProtectKeywordValue ProtectDigestMethodInEffect(
    const ProtectKeywordScope& scope) {
  ProtectKeywordValue written = scope.ValueOf(kDigestMethodKeyword);
  if (!written.defaulted && !written.value.empty()) return written;
  return {std::string(kDefaultDigestMethod), true};
}

bool ProtectMessageDigest(std::string_view data, std::string_view identifier,
                          std::string* digest) {
  if (identifier == kSha1DigestMethod) {
    digest->assign(Sha1Digest(data));
    return true;
  }
  if (identifier == kMd5DigestMethod) {
    digest->assign(Md5Digest(data));
    return true;
  }
  return false;
}

}  // namespace delta
