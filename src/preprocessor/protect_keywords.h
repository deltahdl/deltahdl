#pragma once

#include <cstdint>
#include <span>
#include <string>
#include <string_view>
#include <vector>

namespace delta {

struct ProtectPragmaKeyword {
  std::string_view name;
  std::string_view description;
};

std::span<const ProtectPragmaKeyword> ProtectPragmaKeywords();

bool IsProtectPragmaKeyword(std::string_view name);

bool IsProtectStringValuedKeyword(std::string_view name);

std::string_view ProtectPragmaKeywordDescription(std::string_view name);

std::string_view ProtectPragmaValueBody(std::string_view value);

inline constexpr std::string_view kAuthorKeyword = "author";

inline constexpr std::string_view kAuthorInfoKeyword = "author_info";

inline constexpr std::string_view kEncryptAgentKeyword = "encrypt_agent";

inline constexpr std::string_view kEncryptAgentInfoKeyword =
    "encrypt_agent_info";

inline constexpr std::string_view kDataKeynameKeyword = "data_keyname";

inline constexpr std::string_view kDataKeyownerKeyword = "data_keyowner";

inline constexpr std::string_view kDataMethodKeyword = "data_method";

inline constexpr std::string_view kDataPublicKeyKeyword = "data_public_key";
inline constexpr std::string_view kDataDecryptKeyKeyword = "data_decrypt_key";

bool IsProtectKeyDesignationKeyword(std::string_view name);

inline constexpr std::string_view kDigestKeynameKeyword = "digest_keyname";

inline constexpr std::string_view kDigestKeyownerKeyword = "digest_keyowner";

inline constexpr std::string_view kDigestPublicKeyKeyword = "digest_public_key";

bool IsProtectDigestDesignationKeyword(std::string_view name);

inline constexpr std::string_view kKeyKeynameKeyword = "key_keyname";

inline constexpr std::string_view kKeyKeyownerKeyword = "key_keyowner";

inline constexpr std::string_view kKeyPublicKeyKeyword = "key_public_key";

bool IsProtectKeyBlockDesignationKeyword(std::string_view name);

inline constexpr std::string_view kCommentKeyword = "comment";

inline constexpr std::string_view kResetKeyword = "reset";

struct ProtectKeywordValue {
  std::string value;
  bool defaulted;
};

class ProtectKeywordScope {
 public:
  void Apply(std::string_view keyword, std::string_view value);

  ProtectKeywordValue ValueOf(std::string_view keyword) const;

  void Reset();

  ProtectKeywordValue DigestKeynameInEffect() const;

  ProtectKeywordValue DigestKeyownerInEffect() const;

  ProtectKeywordValue DigestPublicKeyInEffect() const;

 private:
  struct Entry {
    std::string keyword;
    std::string value;
  };
  std::vector<Entry> in_effect_;
};

struct ProtectKey {
  std::string owner;
  std::string name;
  std::string key;
};

class ProtectKeyList {
 public:
  void Add(ProtectKey key);

  bool KnowsOwner(std::string_view owner) const;

  bool KnowsKey(std::string_view owner, std::string_view name) const;

  std::string_view KeyFor(std::string_view owner, std::string_view name) const;

  bool Empty() const { return keys_.empty(); }

 private:
  const ProtectKey* Find(std::string_view owner, std::string_view name) const;

  std::vector<ProtectKey> keys_;
};

bool ProtectKeynameReachesNoKey(const ProtectKeyList& keys,
                                std::string_view owner, std::string_view name);

class ProtectKeyDesignations {
 public:
  bool Record(std::string_view owner, std::string_view keyword,
              std::string_view value);

 private:
  struct Designation {
    std::string owner;
    std::string keyword;
    std::string value;
  };
  std::vector<Designation> written_;
};

std::string_view ProtectDigestKey(const ProtectKeywordScope& scope,
                                  const ProtectKeyList& keys);

std::string_view ProtectKeyBlockKey(const ProtectKeywordScope& scope,
                                    const ProtectKeyList& keys);

enum class ProtectKeyAgreement : uint8_t {
  kUndecided,
  kSameKey,
  kDifferentKeys
};

ProtectKeyAgreement ProtectKeyBlockDesignationsAgree(
    const ProtectKeywordScope& scope, const ProtectKeyList& keys);

ProtectKeyAgreement ProtectDataDesignationsAgree(
    const ProtectKeywordScope& scope, const ProtectKeyList& keys);

ProtectKeyAgreement ProtectDigestDesignationsAgree(
    const ProtectKeywordScope& scope, const ProtectKeyList& keys);

std::string ProtectAuthorDirective(std::string_view author);

std::string ProtectAuthorInfoDirective(std::string_view author_info);

std::string ProtectCommentDirective(std::string_view comment);

std::string ProtectDataKeynameDirective(std::string_view keyname);

std::string ProtectDigestKeynameDirective(std::string_view keyname);

std::string ProtectKeyKeynameDirective(std::string_view keyname);

std::string ProtectDataKeyownerDirective(std::string_view keyowner);

std::string ProtectDigestKeyownerDirective(std::string_view keyowner);

std::string ProtectKeyKeyownerDirective(std::string_view keyowner);

std::string ProtectDigestMethodDirective(std::string_view method);

std::string ProtectKeyPublicKeyDirective(std::string_view encoded_key);

std::string ProtectDataPublicKeyDirective(std::string_view encoded_key);

std::string ProtectDigestPublicKeyDirective(std::string_view encoded_key);

struct ProtectEnvelopeDescription {
  std::string_view encrypt_agent;
  std::string_view encrypt_agent_info;
  std::string_view data_method;
  std::string_view encoding;
};

std::string ProtectEnvelopeDescriptionDirectives(
    const ProtectEnvelopeDescription& description);

std::string ProtectKeywordResetDirective();

}  // namespace delta
