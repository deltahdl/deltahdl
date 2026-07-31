#include "preprocessor/protect_keywords.h"

#include <span>
#include <string>
#include <string_view>
#include <utility>

namespace delta {
namespace {

// The table of §34.4. Each entry pairs a name the standard sets aside for the
// protect pragma with what the standard says that name does, and §34.5 writes
// the definition behind each one out in full.
//
// The order is the table's own, which is also the order the definitions are
// written in, so an entry's position here is its definition's position there.
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
    {"decrypt_license", "states what a decryption is licensed on"},
    {"runtime_license", "states what a simulation is licensed on"},
    {"comment", "carries documentation that nothing goes on to interpret"},
    {"reset", "puts the protect pragma keywords back to their defaults"},
    {"viewport", "widens the access a decryption envelope allows into itself"},
};

// The tabulated name of the expression that puts the keywords back to their
// defaults.
constexpr std::string_view kResetKeyword = "reset";

// The three tabulated names by which one key of a stated entity is picked out
// of that entity's keys. They are listed together because what §34.5.10 says
// about them it says about all three at once.
constexpr std::string_view kKeyDesignationKeywords[] = {
    kDataKeynameKeyword, kDataDecryptKeyKeyword, kDataPublicKeyKeyword};

// One directive carrying one keyword and the string that keyword records.
void AppendKeywordDirective(std::string& text, std::string_view keyword,
                            std::string_view value) {
  text.append("`pragma protect ").append(keyword).append("=\"");
  text.append(value).append("\"\n");
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
  for (std::string_view keyword : kKeyDesignationKeywords) {
    if (keyword == name) return true;
  }
  return false;
}

// A value already written for this entity against one of the other designating
// names would have to pick out a second of that entity's keys, so it picks out
// neither and the writing is not unique. The same value under another entity
// is read against another list of keys and is no repetition of anything.
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
  AppendKeywordDirective(text, kDataKeyownerKeyword,
                         ProtectPragmaValueBody(keyowner));
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

// Both halves are read where the reading stands rather than at the point the
// keys were supplied, because a text may name one entity for one region and
// another for the next, and the name of the key is read against whichever
// entity is in effect beside it.
std::string_view ProtectDigestKey(const ProtectKeywordScope& scope,
                                  const ProtectKeyList& keys) {
  ProtectKeywordValue owner = scope.ValueOf(kDigestKeyownerKeyword);
  ProtectKeywordValue name = scope.DigestKeynameInEffect();
  return keys.KeyFor(owner.value, name.value);
}

// Both halves are read where the reading stands, for the same reason: a text
// may name one entity for one region and another for the next, and the name of
// the key is read against whichever entity is in effect beside it.
std::string_view ProtectKeyBlockKey(const ProtectKeywordScope& scope,
                                    const ProtectKeyList& keys) {
  ProtectKeywordValue owner = scope.ValueOf(kKeyKeyownerKeyword);
  ProtectKeywordValue name = scope.ValueOf(kKeyKeynameKeyword);
  return keys.KeyFor(owner.value, name.value);
}

std::string ProtectEnvelopeDescriptionDirectives(
    const ProtectEnvelopeDescription& description) {
  std::string text;
  AppendKeywordDirective(text, "encrypt_agent", description.encrypt_agent);
  AppendKeywordDirective(text, "data_method", description.data_method);
  // The coding scheme is written as a subkeyword of the encoding keyword's
  // value rather than as the keyword's own value.
  text.append("`pragma protect encoding=(enctype=\"");
  text.append(description.encoding).append("\")\n");
  return text;
}

std::string ProtectKeywordResetDirective() {
  std::string text;
  text.append("`pragma protect ").append(kResetKeyword).append("\n");
  return text;
}

// A keyword written again keeps the entry it already has, because what is in
// effect for it is the most recent writing of it rather than the first.
void ProtectKeywordScope::Apply(std::string_view keyword,
                                std::string_view value) {
  if (!IsProtectPragmaKeyword(keyword)) return;
  std::string_view body = ProtectPragmaValueBody(value);
  for (Entry& entry : in_effect_) {
    if (entry.keyword == keyword) {
      entry.value = std::string(body);
      return;
    }
  }
  in_effect_.push_back({std::string(keyword), std::string(body)});
}

// A keyword no directive has written has no entry, and what stands in its
// place is its default value.
ProtectKeywordValue ProtectKeywordScope::ValueOf(
    std::string_view keyword) const {
  for (const Entry& entry : in_effect_) {
    if (entry.keyword == keyword) return {entry.value, false};
  }
  return {std::string(), true};
}

// A digest_keyname a directive gave a name stands as it was written. With no
// name given there is still a key the digest is under, and it is the one the
// data are under, so the name of that key is what fills the place rather than
// nothing at all. What fills it is a default, and it is reported as one.
//
// What decides between the two is whether a name was specified, not whether
// the keyword was mentioned: the keyword written with nothing against it named
// no key any more than leaving it out did, so the same value fills the place
// either way.
ProtectKeywordValue ProtectKeywordScope::DigestKeynameInEffect() const {
  ProtectKeywordValue written = ValueOf(kDigestKeynameKeyword);
  if (!written.defaulted && !written.value.empty()) return written;
  return {ValueOf(kDataKeynameKeyword).value, true};
}

}  // namespace delta
