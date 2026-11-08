#include "preprocessor/protect_digest_block.h"

#include <string>
#include <string_view>

#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

namespace delta {

std::string ProtectDigestBlockDirectives(std::string_view cleartext,
                                         const ProtectDigestBlockPolicy& policy,
                                         const ProtectEncoding& encoding) {
  std::string text;
  if (!policy.requested || policy.key.empty()) return text;
  std::string digest;
  if (!ProtectMessageDigest(cleartext, policy.method, &digest)) return text;
  text.append(ProtectEncodedValueDirective(
      encoding, ProtectedRegionBlockSize(digest, policy.cipher)));
  text.append("`pragma protect ").append(kDigestBlockKeyword).append("\n");
  text.append(EncryptProtectedRegion(digest, policy.key, encoding.enctype,
                                     policy.cipher));
  text.push_back('\n');
  return text;
}

ProtectDigestCheck CheckProtectDigestBlock(std::string_view block,
                                           const ProtectDigestTarget& target,
                                           std::string_view method,
                                           std::string_view cipher) {
  std::string carried;
  if (!DecryptProtectedBlock(block, target.key, &carried, cipher)) {
    return ProtectDigestCheck::kUnreadable;
  }
  std::string regenerated;
  if (!ProtectMessageDigest(target.cleartext, method, &regenerated)) {
    return ProtectDigestCheck::kUnreadable;
  }
  if (carried == regenerated) return ProtectDigestCheck::kMatched;
  return ProtectDigestCheck::kAltered;
}

std::string_view ProtectDigestKeyByPublicKey(const ProtectKeywordScope& scope,
                                             const ProtectKeyList& keys) {
  ProtectKeywordValue public_key = scope.DigestPublicKeyInEffect();
  if (public_key.value.empty()) return {};
  return keys.KeyFor(scope.DigestKeyownerInEffect().value, public_key.value);
}

}  // namespace delta
