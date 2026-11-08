#include "preprocessor/protect_digest_key.h"

#include <string>
#include <string_view>

#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_keywords.h"

namespace delta {
namespace {

void AppendDirectiveAsWritten(std::string& text, std::string_view keyword,
                              std::string_view value) {
  text.append("`pragma protect ").append(keyword).append("=");
  text.append(value).append("\n");
}

}  // namespace

bool IsProtectDigestKeyMethodIdentifier(std::string_view identifier) {
  return IsProtectKeyMethodIdentifier(identifier);
}

ProtectKeywordValue ProtectDigestKeyMethodInEffect(
    const ProtectKeywordScope& scope) {
  ProtectKeywordValue written = scope.ValueOf(kDigestKeyMethodKeyword);
  if (!written.defaulted && !written.value.empty()) return written;
  return {scope.ValueOf(kDataMethodKeyword).value, true};
}

std::string ProtectDigestKeyMethodDirective(std::string_view method) {
  std::string text;
  AppendDirectiveAsWritten(text, kDigestKeyMethodKeyword, method);
  return text;
}

std::string ProtectDigestDecryptKeyDirective(std::string_view encoded_key) {
  std::string text;
  text.append("`pragma protect ").append(kDigestDecryptKeyKeyword).append("\n");
  text.append(encoded_key).append("\n");
  return text;
}

std::string ProtectDigestDecryptionContent(
    const ProtectDigestDecryption& digest, const ProtectEncoding& encoding) {
  std::string text;
  if (!digest.key_method.empty()) {
    AppendDirectiveAsWritten(text, kDigestKeyMethodKeyword, digest.key_method);
  }
  if (!digest.keyname.empty()) {
    text.append(ProtectDigestKeynameDirective(digest.keyname));
  }
  if (!digest.digest_method.empty()) {
    AppendDirectiveAsWritten(text, kDigestMethodKeyword, digest.digest_method);
  }
  if (!digest.decrypt_key.empty()) {
    text.append(
        ProtectEncodedValueDirective(encoding, digest.decrypt_key.size()));
    text.append(ProtectDigestDecryptKeyDirective(
        EncodeProtectValue(digest.decrypt_key, encoding)));
  }
  return text;
}

}  // namespace delta
