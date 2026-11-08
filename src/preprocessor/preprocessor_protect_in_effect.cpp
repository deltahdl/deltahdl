#include <string>
#include <string_view>

#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"

namespace delta {

std::string_view Preprocessor::ProtectKeyInEffect() const {
  if (!data_decrypt_key_.empty()) return data_decrypt_key_;
  if (config_.protect_keys.Empty()) return config_.protect_key;
  ProtectKeywordValue owner = protect_keywords_.ValueOf(kDataKeyownerKeyword);
  ProtectKeywordValue name = protect_keywords_.ValueOf(kDataKeynameKeyword);
  std::string_view named = config_.protect_keys.KeyFor(owner.value, name.value);
  if (!named.empty()) return named;
  ProtectKeywordValue public_key =
      protect_keywords_.ValueOf(kDataPublicKeyKeyword);
  std::string_view under_public =
      config_.protect_keys.KeyFor(owner.value, public_key.value);
  if (!under_public.empty()) return under_public;
  return ProtectKeyBlockKey(protect_keywords_, config_.protect_keys);
}

std::string_view Preprocessor::DigestKeyInEffect() const {
  if (config_.protect_keys.Empty()) return config_.protect_key;
  return ProtectDigestKey(protect_keywords_, config_.protect_keys);
}

std::string_view Preprocessor::DigestDecryptKeyInEffect() const {
  if (!digest_decrypt_key_.empty()) return digest_decrypt_key_;
  return data_decrypt_key_;
}

std::string_view Preprocessor::DigestBlockKeyInEffect() const {
  std::string_view carried = DigestDecryptKeyInEffect();
  if (!carried.empty()) return carried;
  std::string_view named = DigestKeyInEffect();
  if (!named.empty()) return named;
  std::string_view under_public =
      ProtectDigestKeyByPublicKey(protect_keywords_, config_.protect_keys);
  if (!under_public.empty()) return under_public;
  return ProtectKeyInEffect();
}

std::string Preprocessor::DigestMethodInEffect() const {
  return ProtectDigestMethodInEffect(protect_keywords_).value;
}

ProtectEncoding Preprocessor::ProtectEncodingInEffect() const {
  ProtectEncoding encoding =
      ParseProtectEncoding(protect_keywords_.ValueOf(kEncodingKeyword).value);
  if (encoding.enctype.empty()) {
    encoding.enctype = DefaultProtectEncoding().enctype;
  }
  return encoding;
}

}  // namespace delta
