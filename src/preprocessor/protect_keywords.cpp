#include "preprocessor/protect_keywords.h"

#include <span>
#include <string>
#include <string_view>
#include <utility>

#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_license.h"
#include "preprocessor/protect_pragma_line.h"

namespace delta {
namespace {

constexpr ProtectPragmaKeyword kProtectPragmaKeywords[] = {
    {"begin", "starts an envelope for encryption"},
    {"end", "finishes an envelope for encryption"},
    {"begin_protected", "starts an envelope for decryption"},
    {"end_protected", "finishes an envelope for decryption"},
    {"author", "names who wrote the design an envelope carries"},
    {"author_info", "carries anything further about that author"},
    {"encrypt_agent", "names the service that performed the encryption"},
    {"encrypt_agent_info", "carries anything further about that service"},
    {"encoding", "gives the coding scheme the encrypted data are written in"},
    {"data_keyowner", "names who holds the key that encrypts the data"},
    {"data_method", "names the algorithm that encrypts the data"},
    {"data_keyname", "names the key that encrypts the data"},
    {"data_public_key", "gives the public key that encrypts the data"},
    {"data_decrypt_key", "gives the session key for the data"},
    {"data_block", "starts an encoded block holding the encrypted data"},
    {"digest_keyowner", "names who holds the key that encrypts the digest"},
    {"digest_key_method", "names the algorithm that encrypts the digest key"},
    {"digest_keyname", "names the key that encrypts the digest"},
    {"digest_public_key", "gives the public key that encrypts the digest"},
    {"digest_decrypt_key", "gives the session key for the digest"},
    {"digest_method", "names the algorithm that computes the digest"},
    {"digest_block", "gives a digest the data can be checked against"},
    {"key_keyowner", "names who holds the key that encrypts the keys"},
    {"key_method", "names the algorithm that encrypts the keys"},
    {"key_keyname", "names the key that encrypts the keys"},
    {"key_public_key", "gives the public key that encrypts the keys"},
    {"key_block", "starts an encoded block holding the key data"},
    {kDecryptLicenseKeyword, "states what a decryption is licensed on"},
    {kRuntimeLicenseKeyword, "states what a simulation is licensed on"},
    {kCommentKeyword,
     "carries documentation that nothing goes on to interpret"},
    {kResetKeyword, "puts the protect pragma keywords back to their defaults"},
    {"viewport", "widens the access a decryption envelope allows into itself"},
};

constexpr std::string_view kKeyDesignationKeywords[] = {
    kDataKeynameKeyword, kDataDecryptKeyKeyword, kDataPublicKeyKeyword};

constexpr std::string_view kKeyBlockDesignationKeywords[] = {
    kKeyKeynameKeyword, kKeyPublicKeyKeyword};

constexpr std::string_view kDigestDesignationKeywords[] = {
    kDigestKeynameKeyword, kDigestDecryptKeyKeyword, kDigestPublicKeyKeyword};

bool IsOneOf(std::span<const std::string_view> listed, std::string_view name) {
  for (std::string_view candidate : listed) {
    if (candidate == name) return true;
  }
  return false;
}

void AppendKeywordDirective(std::string& text, std::string_view keyword,
                            std::string_view value) {
  text.append("`pragma protect ").append(keyword).append("=\"");
  text.append(value).append("\"\n");
}

void AppendKeywordDirectiveAsWritten(std::string& text,
                                     std::string_view keyword,
                                     std::string_view value) {
  text.append("`pragma protect ").append(keyword).append("=");
  text.append(value).append("\n");
}

ProtectKeyAgreement DesignationsAgree(const ProtectKeyList& keys,
                                      std::string_view owner,
                                      std::string_view first,
                                      std::string_view second) {
  if (first.empty() || second.empty()) return ProtectKeyAgreement::kUndecided;
  std::string_view under_first = keys.KeyFor(owner, first);
  std::string_view under_second = keys.KeyFor(owner, second);
  if (under_first.empty() || under_second.empty()) {
    return ProtectKeyAgreement::kUndecided;
  }
  if (under_first == under_second) return ProtectKeyAgreement::kSameKey;
  return ProtectKeyAgreement::kDifferentKeys;
}

const ProtectPragmaKeyword* FindProtectPragmaKeyword(std::string_view name) {
  for (const ProtectPragmaKeyword& keyword : kProtectPragmaKeywords) {
    if (keyword.name == name) return &keyword;
  }
  return nullptr;
}

}  // namespace

std::span<const ProtectPragmaKeyword> ProtectPragmaKeywords() {
  return kProtectPragmaKeywords;
}

constexpr std::string_view kStringValuedKeywords[] = {
    kAuthorKeyword,           kAuthorInfoKeyword,     kEncryptAgentKeyword,
    kEncryptAgentInfoKeyword, kDataKeyownerKeyword,   kDataMethodKeyword,
    kDataKeynameKeyword,      kDigestKeyownerKeyword, kDigestKeyMethodKeyword,
    kDigestKeynameKeyword,    kDigestMethodKeyword,   kKeyKeyownerKeyword,
    kKeyMethodKeyword,        kKeyKeynameKeyword,     kCommentKeyword,
};

bool ProtectKeynameReachesNoKey(const ProtectKeyList& keys,
                                std::string_view owner, std::string_view name) {
  if (name.empty()) return false;
  if (!keys.KnowsOwner(owner)) return false;
  return !keys.KnowsKey(owner, name);
}

bool IsProtectStringValuedKeyword(std::string_view name) {
  for (std::string_view keyword : kStringValuedKeywords) {
    if (keyword == name) return true;
  }
  return false;
}

bool IsProtectPragmaKeyword(std::string_view name) {
  return FindProtectPragmaKeyword(name) != nullptr;
}

std::string_view ProtectPragmaKeywordDescription(std::string_view name) {
  const ProtectPragmaKeyword* keyword = FindProtectPragmaKeyword(name);
  if (keyword == nullptr) return {};
  return keyword->description;
}

std::string_view ProtectPragmaValueBody(std::string_view value) {
  if (value.size() >= 2 && value.front() == '"' && value.back() == '"') {
    return value.substr(1, value.size() - 2);
  }
  return value;
}

bool IsProtectKeyDesignationKeyword(std::string_view name) {
  return IsOneOf(kKeyDesignationKeywords, name);
}

bool IsProtectKeyBlockDesignationKeyword(std::string_view name) {
  return IsOneOf(kKeyBlockDesignationKeywords, name);
}

bool IsProtectDigestDesignationKeyword(std::string_view name) {
  return IsOneOf(kDigestDesignationKeywords, name);
}

bool ProtectKeyDesignations::Record(std::string_view owner,
                                    std::string_view keyword,
                                    std::string_view value) {
  bool unique = true;
  for (const Designation& earlier : written_) {
    if (earlier.owner == owner && earlier.value == value &&
        earlier.keyword != keyword) {
      unique = false;
      break;
    }
  }
  Designation designation;
  designation.owner = owner;
  designation.keyword = keyword;
  designation.value = value;
  written_.push_back(std::move(designation));
  return unique;
}

std::string ProtectAuthorDirective(std::string_view author) {
  std::string text;
  AppendKeywordDirectiveAsWritten(text, kAuthorKeyword, author);
  return text;
}

std::string ProtectAuthorInfoDirective(std::string_view author_info) {
  std::string text;
  AppendKeywordDirectiveAsWritten(text, kAuthorInfoKeyword, author_info);
  return text;
}

std::string ProtectCommentDirective(std::string_view comment) {
  std::string text;
  AppendKeywordDirectiveAsWritten(text, kCommentKeyword, comment);
  return text;
}

std::string ProtectDataKeynameDirective(std::string_view keyname) {
  std::string text;
  AppendKeywordDirective(text, kDataKeynameKeyword,
                         ProtectPragmaValueBody(keyname));
  return text;
}

std::string ProtectDigestKeynameDirective(std::string_view keyname) {
  std::string text;
  AppendKeywordDirective(text, kDigestKeynameKeyword,
                         ProtectPragmaValueBody(keyname));
  return text;
}

std::string ProtectKeyKeynameDirective(std::string_view keyname) {
  std::string text;
  AppendKeywordDirective(text, kKeyKeynameKeyword,
                         ProtectPragmaValueBody(keyname));
  return text;
}

std::string ProtectDataKeyownerDirective(std::string_view keyowner) {
  std::string text;
  AppendKeywordDirectiveAsWritten(text, kDataKeyownerKeyword, keyowner);
  return text;
}

std::string ProtectDigestKeyownerDirective(std::string_view keyowner) {
  std::string text;
  AppendKeywordDirectiveAsWritten(text, kDigestKeyownerKeyword, keyowner);
  return text;
}

std::string ProtectKeyKeyownerDirective(std::string_view keyowner) {
  std::string text;
  AppendKeywordDirectiveAsWritten(text, kKeyKeyownerKeyword, keyowner);
  return text;
}

std::string ProtectDigestMethodDirective(std::string_view method) {
  std::string text;
  AppendKeywordDirectiveAsWritten(text, kDigestMethodKeyword, method);
  return text;
}

std::string ProtectKeyPublicKeyDirective(std::string_view encoded_key) {
  std::string text;
  text.append("`pragma protect ").append(kKeyPublicKeyKeyword).append("\n");
  text.append(encoded_key).append("\n");
  return text;
}

std::string ProtectDataPublicKeyDirective(std::string_view encoded_key) {
  std::string text;
  text.append("`pragma protect ").append(kDataPublicKeyKeyword).append("\n");
  text.append(encoded_key).append("\n");
  return text;
}

std::string ProtectDigestPublicKeyDirective(std::string_view encoded_key) {
  std::string text;
  text.append("`pragma protect ").append(kDigestPublicKeyKeyword).append("\n");
  text.append(encoded_key).append("\n");
  return text;
}

void ProtectKeyList::Add(ProtectKey key) { keys_.push_back(std::move(key)); }

const ProtectKey* ProtectKeyList::Find(std::string_view owner,
                                       std::string_view name) const {
  for (const ProtectKey& key : keys_) {
    if (key.owner == owner && key.name == name) return &key;
  }
  return nullptr;
}

bool ProtectKeyList::KnowsOwner(std::string_view owner) const {
  for (const ProtectKey& key : keys_) {
    if (key.owner == owner) return true;
  }
  return false;
}

bool ProtectKeyList::KnowsKey(std::string_view owner,
                              std::string_view name) const {
  return Find(owner, name) != nullptr;
}

std::string_view ProtectKeyList::KeyFor(std::string_view owner,
                                        std::string_view name) const {
  const ProtectKey* key = Find(owner, name);
  if (key == nullptr) return {};
  return key->key;
}

std::string_view ProtectDigestKey(const ProtectKeywordScope& scope,
                                  const ProtectKeyList& keys) {
  ProtectKeywordValue owner = scope.DigestKeyownerInEffect();
  ProtectKeywordValue name = scope.DigestKeynameInEffect();
  return keys.KeyFor(owner.value, name.value);
}

std::string_view ProtectKeyBlockKey(const ProtectKeywordScope& scope,
                                    const ProtectKeyList& keys) {
  ProtectKeywordValue owner = scope.ValueOf(kKeyKeyownerKeyword);
  ProtectKeywordValue name = scope.ValueOf(kKeyKeynameKeyword);
  std::string_view under_name = keys.KeyFor(owner.value, name.value);
  if (!under_name.empty()) return under_name;
  ProtectKeywordValue public_key = scope.ValueOf(kKeyPublicKeyKeyword);
  return keys.KeyFor(owner.value, public_key.value);
}

ProtectKeyAgreement ProtectKeyBlockDesignationsAgree(
    const ProtectKeywordScope& scope, const ProtectKeyList& keys) {
  ProtectKeywordValue owner = scope.ValueOf(kKeyKeyownerKeyword);
  ProtectKeywordValue name = scope.ValueOf(kKeyKeynameKeyword);
  ProtectKeywordValue public_key = scope.ValueOf(kKeyPublicKeyKeyword);
  return DesignationsAgree(keys, owner.value, name.value, public_key.value);
}

ProtectKeyAgreement ProtectDataDesignationsAgree(
    const ProtectKeywordScope& scope, const ProtectKeyList& keys) {
  ProtectKeywordValue owner = scope.ValueOf(kDataKeyownerKeyword);
  ProtectKeywordValue name = scope.ValueOf(kDataKeynameKeyword);
  ProtectKeywordValue public_key = scope.ValueOf(kDataPublicKeyKeyword);
  return DesignationsAgree(keys, owner.value, name.value, public_key.value);
}

ProtectKeyAgreement ProtectDigestDesignationsAgree(
    const ProtectKeywordScope& scope, const ProtectKeyList& keys) {
  ProtectKeywordValue owner = scope.DigestKeyownerInEffect();
  ProtectKeywordValue name = scope.ValueOf(kDigestKeynameKeyword);
  ProtectKeywordValue public_key = scope.ValueOf(kDigestPublicKeyKeyword);
  return DesignationsAgree(keys, owner.value, name.value, public_key.value);
}

std::string ProtectEnvelopeDescriptionDirectives(
    const ProtectEnvelopeDescription& description) {
  std::string text;
  AppendKeywordDirective(text, kEncryptAgentKeyword, description.encrypt_agent);
  if (!description.encrypt_agent_info.empty()) {
    AppendKeywordDirective(text, kEncryptAgentInfoKeyword,
                           description.encrypt_agent_info);
  }
  if (!description.data_method.empty()) {
    AppendKeywordDirective(text, "data_method", description.data_method);
  }
  text.append("`pragma protect ").append(kEncodingKeyword).append("=");
  text.append(description.encoding).append("\n");
  return text;
}

std::string ProtectKeywordResetDirective() {
  std::string text;
  text.append("`pragma protect ").append(kResetKeyword).append("\n");
  return text;
}

void ProtectKeywordScope::Apply(std::string_view keyword,
                                std::string_view value) {
  if (!IsProtectPragmaKeyword(keyword)) return;
  if (IsProtectStringValuedKeyword(keyword) &&
      IsParenthesizedPragmaValue(value)) {
    return;
  }
  std::string_view body = ProtectPragmaValueBody(value);
  for (Entry& entry : in_effect_) {
    if (entry.keyword == keyword) {
      entry.value = std::string(body);
      return;
    }
  }
  in_effect_.push_back({std::string(keyword), std::string(body)});
}

void ProtectKeywordScope::Reset() { in_effect_.clear(); }

ProtectKeywordValue ProtectKeywordScope::ValueOf(
    std::string_view keyword) const {
  for (const Entry& entry : in_effect_) {
    if (entry.keyword == keyword) return {entry.value, false};
  }
  return {std::string(), true};
}

ProtectKeywordValue ProtectKeywordScope::DigestKeynameInEffect() const {
  ProtectKeywordValue written = ValueOf(kDigestKeynameKeyword);
  if (!written.defaulted && !written.value.empty()) return written;
  return {ValueOf(kDataKeynameKeyword).value, true};
}

ProtectKeywordValue ProtectKeywordScope::DigestKeyownerInEffect() const {
  ProtectKeywordValue written = ValueOf(kDigestKeyownerKeyword);
  if (!written.defaulted && !written.value.empty()) return written;
  return {ValueOf(kDataKeyownerKeyword).value, true};
}

ProtectKeywordValue ProtectKeywordScope::DigestPublicKeyInEffect() const {
  ProtectKeywordValue written = ValueOf(kDigestPublicKeyKeyword);
  if (!written.defaulted && !written.value.empty()) return written;
  return {ValueOf(kDataPublicKeyKeyword).value, true};
}

}  // namespace delta
