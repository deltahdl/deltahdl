#include "preprocessor/protect_digest.h"

#include <span>
#include <string>
#include <string_view>

#include "preprocessor/protect_digest_algorithms.h"
#include "preprocessor/protect_keywords.h"

namespace delta {
namespace {

// Table 34-4, in the order the table lists them: the identifier, whether every
// implementation provides the algorithm behind it, and the published algorithm
// the identifier stands for.
//
// The two marked required are the ones a tool may be handed a digest under
// without having been told anything about the tool that computed it. The two
// marked optional are named here without being provided, which is what the
// optional column allows: what the table asks of an implementation offering one
// of them is that it offer it under this name rather than a name of its own.
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

// The identifiers this implementation has an algorithm for are exactly the ones
// the table requires of every implementation. An optional identifier is
// tabulated all the same, so being outside this answer says nothing about being
// outside the table.
bool ProtectDigestIsAvailable(std::string_view identifier) {
  return IsRequiredProtectDigestAlgorithm(identifier);
}

// A directive that wrote the keyword with nothing against it named no algorithm
// any more than leaving the keyword out did, so the default fills the place in
// both cases and is reported as a default in both.
ProtectKeywordValue ProtectDigestMethodInEffect(
    const ProtectKeywordScope& scope) {
  ProtectKeywordValue written = scope.ValueOf(kDigestMethodKeyword);
  if (!written.defaulted && !written.value.empty()) return written;
  return {std::string(kDefaultDigestMethod), true};
}

// The identifier decides the computation and nothing else does. An identifier
// this implementation has no algorithm for therefore produces no digest at all
// rather than one under some algorithm it does have, a digest being the value
// the named algorithm produces.
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
