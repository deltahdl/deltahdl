#include "preprocessor/protect_digest_block.h"

#include <cstddef>
#include <string>
#include <string_view>

#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

namespace delta {

// The digest is computed from the cleartext of the block rather than from the
// characters the block was written as, because that is what a reader has to
// recompute it from: a reader holds the design once it has opened the block,
// and the characters it opened are not the same characters twice unless the two
// tools also agree on a cipher, a key and a coding scheme.
//
// The cipher this implementation encrypts a digest under is a stream cipher and
// asks for no initialization vector, so the cipher-block §34.5.22 has prepended
// to a digest encrypted under a CBC algorithm has nothing here to be prepended
// to. A tool offering such a cipher writes it ahead of the digest before the
// encoding is applied; one that does not, as here, writes the digest alone.
std::string ProtectDigestBlockDirectives(std::string_view cleartext,
                                         const ProtectDigestBlockPolicy& policy,
                                         const ProtectEncoding& encoding) {
  std::string text;
  if (!policy.requested || policy.key.empty()) return text;
  std::string digest;
  if (!ProtectMessageDigest(cleartext, policy.method, &digest)) return text;
  // §34.5.9 has the count stated ahead of each block a tool writes, and a
  // digest is a block of its own: an envelope carrying a digest for each of its
  // blocks writes one of these ahead of each rather than one for them all.
  text.append(
      ProtectEncodedValueDirective(encoding, ProtectedRegionBlockSize(digest)));
  text.append("`pragma protect ").append(kDigestBlockKeyword).append("\n");
  text.append(EncryptProtectedRegion(digest, policy.key, encoding.enctype));
  text.push_back('\n');
  return text;
}

// The two halves are asked in the order §34.5.22 asks them: the digest a block
// carries is recovered first, and the digest of the data is generated second,
// so that a block nothing here can open is told apart from a block whose digest
// disagrees with the data beside it.
//
// The same stream cipher opens the digest, so the initialization vector
// §34.5.22 has removed from the front of a digest encrypted under a CBC
// algorithm is not there to be removed and the whole of the decoded block is
// the digest.
ProtectDigestCheck CheckProtectDigestBlock(std::string_view block,
                                           const ProtectDigestTarget& target,
                                           std::string_view method) {
  std::string carried;
  if (!DecryptProtectedBlock(block, target.key, &carried)) {
    return ProtectDigestCheck::kUnreadable;
  }
  std::string regenerated;
  if (!ProtectMessageDigest(target.cleartext, method, &regenerated)) {
    return ProtectDigestCheck::kUnreadable;
  }
  if (carried == regenerated) return ProtectDigestCheck::kMatched;
  return ProtectDigestCheck::kAltered;
}

// Both halves are read where the reading stands rather than at the point the
// keys were supplied, because a text may name one entity for one region and
// another for the next, and a designation is read against whichever entity is
// in effect beside it.
//
// A region that designated no public key for its digest is told apart from one
// whose designation reaches none of the keys held, and only by asking first: an
// empty designation read against an entity would otherwise select whichever key
// that entity happened to be holding under an empty name.
//
// The entity is the one §34.5.16 leaves in effect rather than the one a
// directive happened to write. That subclause combines the entity with this
// designation as much as with the name given to a key, and it fills an entity
// the text left unnamed from the one whose key the region's data are under, so
// a designation read against the empty entity would find none of the keys the
// text really reached for.
//
// The designation is likewise the one §34.5.19 leaves in effect. A text that
// designated no public key for its digest is read under the public key its data
// are under, so a text saying nothing about its digest's public key has still
// designated one, and the pair reaches the key such a text really asked for.
std::string_view ProtectDigestKeyByPublicKey(const ProtectKeywordScope& scope,
                                             const ProtectKeyList& keys) {
  ProtectKeywordValue public_key = scope.DigestPublicKeyInEffect();
  if (public_key.value.empty()) return {};
  return keys.KeyFor(scope.DigestKeyownerInEffect().value, public_key.value);
}

}  // namespace delta
