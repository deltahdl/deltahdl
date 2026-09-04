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
    {kDecryptLicenseKeyword, "states what a decryption is licensed on"},
    {kRuntimeLicenseKeyword, "states what a simulation is licensed on"},
    {kCommentKeyword,
     "carries documentation that nothing goes on to interpret"},
    {kResetKeyword, "puts the protect pragma keywords back to their defaults"},
    {"viewport", "widens the access a decryption envelope allows into itself"},
};

// The three tabulated names by which one key of a stated entity is picked out
// of that entity's keys. They are listed together because what §34.5.10 says
// about them it says about all three at once.
constexpr std::string_view kKeyDesignationKeywords[] = {
    kDataKeynameKeyword, kDataDecryptKeyKeyword, kDataPublicKeyKeyword};

// The two tabulated names by which one key of the entity that provided a
// region's own keys is picked out. §34.5.23 carries the requirement §34.5.10
// makes of the first entity's designations over to this one, and these are the
// designations it ranges over here: the key family tabulates no session key,
// so there is no third name for it to reach.
constexpr std::string_view kKeyBlockDesignationKeywords[] = {
    kKeyKeynameKeyword, kKeyPublicKeyKeyword};

// The three tabulated names by which one key of the entity a digest names is
// picked out of that entity's keys. §34.5.16 says of all three at once that
// their values are unique for that entity, so they are listed together the way
// the three written for the entity the data name are.
constexpr std::string_view kDigestDesignationKeywords[] = {
    kDigestKeynameKeyword, kDigestDecryptKeyKeyword, kDigestPublicKeyKeyword};

// Whether `name` is one of `listed`.
bool IsOneOf(std::span<const std::string_view> listed, std::string_view name) {
  for (std::string_view candidate : listed) {
    if (candidate == name) return true;
  }
  return false;
}

// One directive carrying one keyword and the string that keyword records.
void AppendKeywordDirective(std::string& text, std::string_view keyword,
                            std::string_view value) {
  text.append("`pragma protect ").append(keyword).append("=\"");
  text.append(value).append("\"\n");
}

// The same, for a keyword whose definition has its value unchanged in the file
// a tool writes out: `value` is the pragma_value as the source spelled it, and
// it goes back the way it came.
//
// §22.5.1 gives a pragma_value more than one spelling, and a keyword recording
// a string is not thereby barred from being written with an identifier or a
// number against it. Settling on one spelling would leave a value spelled
// another way rewritten -- a name written bare coming back in quotes -- which
// is a change to the very thing such a keyword is required not to change.
void AppendKeywordDirectiveAsWritten(std::string& text,
                                     std::string_view keyword,
                                     std::string_view value) {
  text.append("`pragma protect ").append(keyword).append("=");
  text.append(value).append("\n");
}

// Whether two designations written for one entity's keys pick out one of that
// entity's keys or two of them.
//
// Both are read against the single list `owner` names, that being the list a
// designation is a member of, and the question is only decided where the tool
// holds a key under each: with one designation reaching nothing there is no
// second key for the first to disagree with. A designation the text never wrote
// reaches nothing in the same way, so it leaves the other standing alone rather
// than disagreeing with it.
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

// Every keyword §34.4 tabulates whose own subclause defines its expression as
// `keyword = <string>`. Each was read there before it was written here:
// §34.5.5.1 author, §34.5.6.1 author_info, §34.5.7.1 encrypt_agent, §34.5.8.1
// encrypt_agent_info, §34.5.10.1 data_keyowner, §34.5.11.1 data_method,
// §34.5.12.1 data_keyname, §34.5.16.1 digest_keyowner, §34.5.17.1
// digest_key_method, §34.5.18.1 digest_keyname, §34.5.21.1 digest_method,
// §34.5.23.1 key_keyowner, §34.5.24.1 key_method, §34.5.25.1 key_keyname and
// §34.5.30.1 comment.
//
// Three tabulated keywords take a value and are absent, their subclauses
// defining them with a parenthesized list rather than a string. §34.5.9.1
// defines `encoding = (enctype = <string> [, ...])`. §34.5.28.1 defines
// `decrypt_license = ( library = <string> , entry = <string> , feature =
// <string> [, exit = <string>] [, match = <number> ] )`, and §34.5.29.1 defines
// runtime_license with the same five parts. A list is the value each of those
// three takes, so refusing one would refuse everything they are ever written
// with.
//
// This is the reading a consuming tool makes. TakeKeyDesignations and
// TakeMethodKeywords in src/preprocessor/protect_region_lines.cpp are the
// reading an encrypting tool makes, and they answer the same question by
// calling KeywordSingleValueOnLine rather than by asking this: a keyword is
// read off a line there rather than off a pragma expression, so there is no
// PragmaKeywordExpression for the two readings to share. Every name in this
// list that an encrypting tool reads off a line is read there through that
// call, so the two readings now answer alike.
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

// §34.5.5 has the expression itself placed in the directive, so the value goes
// out spelled as the source spelled it rather than in whichever spelling this
// file settles on elsewhere: §22.5.1 gives a pragma_value more than one
// spelling, and a name written bare and returned in quotes is a different
// pragma_value from the one the source placed there.
std::string ProtectAuthorDirective(std::string_view author) {
  std::string text;
  AppendKeywordDirectiveAsWritten(text, kAuthorKeyword, author);
  return text;
}

// §34.5.6 has the expression itself placed in the directive, so the value goes
// out spelled as the source spelled it, for the reason the author's own name
// does: §22.5.1 gives a pragma_value more than one spelling, and a value
// written bare and returned in quotes is a different pragma_value from the one
// the source placed there.
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
  // §34.5.10.2: the data_keyowner is unchanged in the output file, and a value
  // is what it was written as rather than what it means -- rewriting a bare
  // identifier as a string changes the pragma_value the source wrote. The
  // digest and key keyowners beside it are written the same way for the same
  // reason.
  AppendKeywordDirectiveAsWritten(text, kDataKeyownerKeyword, keyowner);
  return text;
}

// §34.5.16.2 asks for the entity's name unchanged in the output file, and the
// exception it makes is a digital signature, under which the name is encrypted
// with the digest_key_method and placed in a digest_key_block. The name is
// written here in either case, because §34.4 defines the keyword names Table
// 34-1 lists and digest_key_block is not among them, so the exception names a
// destination no conforming tool writes and no reader could be required to
// open. §34.5.17.2 and §34.5.21.2 except their identifiers into the key_block,
// which Table 34-1 does list, and this tool sends those two there. The value
// goes out spelled as the source spelled it rather than in whichever spelling
// this file settles on elsewhere: §22.5.1 gives a pragma_value more than one
// spelling, and a name written bare and returned in quotes is a different
// pragma_value from the one the author wrote.
std::string ProtectDigestKeyownerDirective(std::string_view keyowner) {
  std::string text;
  AppendKeywordDirectiveAsWritten(text, kDigestKeyownerKeyword, keyowner);
  return text;
}

// §34.5.23 asks for the entity's name unchanged, and states no exception, so
// the value goes out spelled as the source spelled it rather than in whichever
// spelling this file settles on elsewhere. A name written bare and returned in
// quotes would be a different pragma_value from the one the author wrote, and
// the requirement is about the value rather than about what it happens to
// denote.
std::string ProtectKeyKeyownerDirective(std::string_view keyowner) {
  std::string text;
  AppendKeywordDirectiveAsWritten(text, kKeyKeyownerKeyword, keyowner);
  return text;
}

// §34.5.21 asks for the identifier unchanged, and the exception it makes is a
// digital signature, where the identifier is placed in a key block instead of
// standing here. Whichever of the two places it goes to, the value goes out
// spelled as the source spelled it rather than in whichever spelling this file
// settles on elsewhere: §22.5.1 gives a pragma_value more than one spelling,
// and an identifier written bare and returned in quotes is a different
// pragma_value from the one the author wrote.
std::string ProtectDigestMethodDirective(std::string_view method) {
  std::string text;
  AppendKeywordDirectiveAsWritten(text, kDigestMethodKeyword, method);
  return text;
}

// §34.5.24 asks for the identifier unchanged in the output file and makes no
// exception, so the value goes out spelled as the source spelled it rather than
// in whichever spelling this file settles on elsewhere: §22.5.1 gives a
// pragma_value more than one spelling, and an identifier written bare and
// returned in quotes is a different pragma_value from the one the author wrote.
std::string ProtectKeyMethodDirective(std::string_view method) {
  std::string text;
  AppendKeywordDirectiveAsWritten(text, kKeyMethodKeyword, method);
  return text;
}

// The keyword stands alone on its line and the designation follows on the
// next, which is the shape §34.5.26 defines it in. Written against the keyword
// instead, the value would be a pragma_value of the directive, and a reader
// looking where the standard says to look would find the line beneath it
// holding something else.
//
// The whole of that line is the value, so the line goes out carrying what it
// carried. Nothing about it is a pragma_value, and treating it as one would
// let an encoded key that happens to begin and end with a quotation mark come
// back two characters shorter than the key it encodes.
std::string ProtectKeyPublicKeyDirective(std::string_view encoded_key) {
  std::string text;
  text.append("`pragma protect ").append(kKeyPublicKeyKeyword).append("\n");
  text.append(encoded_key).append("\n");
  return text;
}

// The keyword stands alone on its line and the designation follows on the next,
// which is the shape §34.5.13.1 defines it in. Written against the keyword
// instead, the value would be a pragma_value of the directive, and a reader
// looking where the standard says to look would find the line beneath it
// holding something else.
//
// The whole of that line is the value, so the line goes out carrying what it
// carried. Nothing about it is a pragma_value, and treating it as one would let
// an encoded key that happens to begin and end with a quotation mark come back
// two characters shorter than the key it encodes.
std::string ProtectDataPublicKeyDirective(std::string_view encoded_key) {
  std::string text;
  text.append("`pragma protect ").append(kDataPublicKeyKeyword).append("\n");
  text.append(encoded_key).append("\n");
  return text;
}

// The keyword stands alone on its line and the designation follows on the next,
// which is the shape §34.5.19.1 defines it in. Written against the keyword
// instead, the value would be a pragma_value of the directive, and a reader
// looking where the standard says to look would find the line beneath it
// holding something else.
//
// The whole of that line is the value, so the line goes out carrying what it
// carried. Nothing about it is a pragma_value, and treating it as one would let
// an encoded key that happens to begin and end with a quotation mark come back
// two characters shorter than the key it encodes.
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

// Both halves are read where the reading stands rather than at the point the
// keys were supplied, because a text may name one entity for one region and
// another for the next, and the name of the key is read against whichever
// entity is in effect beside it.
//
// The entity is the one §34.5.16 leaves in effect rather than the one a
// directive happened to write, because a text that named a provider for its
// data and none for its digest named one for both: the digest's provider is
// filled from the data's, so a name read against the empty entity would find
// none of the keys the text really reached for.
std::string_view ProtectDigestKey(const ProtectKeywordScope& scope,
                                  const ProtectKeyList& keys) {
  ProtectKeywordValue owner = scope.DigestKeyownerInEffect();
  ProtectKeywordValue name = scope.DigestKeynameInEffect();
  return keys.KeyFor(owner.value, name.value);
}

// Both halves are read where the reading stands, for the same reason: a text
// may name one entity for one region and another for the next, and a
// designation is read against whichever entity is in effect beside it.
//
// The public key is tried where the name reaches nothing, rather than instead
// of it. A text that wrote both wrote two designations of one key, so which of
// them is consulted first decides nothing; a text that wrote only the second
// would be left with no key at all if the first were the only one tried.
std::string_view ProtectKeyBlockKey(const ProtectKeywordScope& scope,
                                    const ProtectKeyList& keys) {
  ProtectKeywordValue owner = scope.ValueOf(kKeyKeyownerKeyword);
  ProtectKeywordValue name = scope.ValueOf(kKeyKeynameKeyword);
  std::string_view under_name = keys.KeyFor(owner.value, name.value);
  if (!under_name.empty()) return under_name;
  ProtectKeywordValue public_key = scope.ValueOf(kKeyPublicKeyKeyword);
  return keys.KeyFor(owner.value, public_key.value);
}

// A designation that was never written picks out nothing, and so does one
// written with nothing against it, so in either case there is only one
// designation in effect and no pair to compare. Where both were written, the
// two are read against the same entity, that being the one whose keys they are
// designations of.
ProtectKeyAgreement ProtectKeyBlockDesignationsAgree(
    const ProtectKeywordScope& scope, const ProtectKeyList& keys) {
  ProtectKeywordValue owner = scope.ValueOf(kKeyKeyownerKeyword);
  ProtectKeywordValue name = scope.ValueOf(kKeyKeynameKeyword);
  ProtectKeywordValue public_key = scope.ValueOf(kKeyPublicKeyKeyword);
  return DesignationsAgree(keys, owner.value, name.value, public_key.value);
}

// The entity here is the one the data name for themselves rather than the one
// named for the region's own keys. The two may differ -- a producer may hold
// them apart -- and a designation reaches a key only through the entity written
// beside it, so a name belonging to one entity's list would stand for a key
// held by another if the wrong list were read.
ProtectKeyAgreement ProtectDataDesignationsAgree(
    const ProtectKeywordScope& scope, const ProtectKeyList& keys) {
  ProtectKeywordValue owner = scope.ValueOf(kDataKeyownerKeyword);
  ProtectKeywordValue name = scope.ValueOf(kDataKeynameKeyword);
  ProtectKeywordValue public_key = scope.ValueOf(kDataPublicKeyKeyword);
  return DesignationsAgree(keys, owner.value, name.value, public_key.value);
}

// The entity here is the one the digest names for itself, filled from the one
// the data name where the digest named none. That is the entity both of these
// designations are read against, a designation being a member of one entity's
// list and standing for a key held by nobody else, so reading them against the
// data provider directly would let a name belonging to a third party's list
// stand for a key that party never held.
//
// The two designations themselves are the ones a directive wrote, not the ones
// standing in their places. §34.5.19 asks this of a text that wrote both, and a
// place filled from the region's data holds a designation that was written for
// the data: comparing it here would report a second time on a pair §34.5.13 has
// already held to referring to one key.
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
  // §34.5.7 has the tool that performed the encryption generate the expression
  // naming itself and place it in a directive the protected envelope encloses.
  // It is generated for every envelope written rather than carried over from
  // the text being encrypted, that text having been written before this tool
  // ever saw it, and it is written here -- in the clear, ahead of the block --
  // rather than among the lines that stop being readable.
  AppendKeywordDirective(text, kEncryptAgentKeyword, description.encrypt_agent);
  // §34.5.8 has whatever further that tool offers about itself placed in a
  // directive the protected envelope encloses as well, and kept out of the data
  // block. It follows the name, that being the order §34.4 tabulates the two
  // in, and it stands in the clear for the reason the name does: a reader
  // holding no key at all still learns what sealed the envelope and what that
  // thing is.
  //
  // The expression is written only where the tool provided a value, the
  // subclause asking for it on that condition. A tool with nothing further to
  // say about itself therefore writes no expression, rather than one carrying
  // an empty string.
  if (!description.encrypt_agent_info.empty()) {
    AppendKeywordDirective(text, kEncryptAgentInfoKeyword,
                           description.encrypt_agent_info);
  }
  // §34.5.11.2 has the cipher a region's data are under "unchanged in the
  // output file, except where a digital signature is used, in which case it is
  // encrypted with the key_method and placed in a key_block". An empty value is
  // that exception in force: the caller passes none where the envelope carries
  // key blocks, ProtectKeyBlockContent (preprocessor/protect_key_block.cpp)
  // having written the cipher into them, and an envelope stating it twice would
  // state in the clear what the signature put inside.
  if (!description.data_method.empty()) {
    AppendKeywordDirective(text, "data_method", description.data_method);
  }
  // The coding scheme is written as a subkeyword of the encoding keyword's
  // value rather than as the keyword's own value, so what the description
  // carries is that whole value and it goes out as it stands.
  text.append("`pragma protect ").append(kEncodingKeyword).append("=");
  text.append(description.encoding).append("\n");
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
  // A keyword defined as `keyword = <string>` is defined with one written
  // thing, so a parenthesized list of further expressions is not the value it
  // takes. An expression writing one states nothing for that keyword.
  //
  // Stating nothing is a different thing from stating an empty value. A text
  // that stated a value earlier is still to be read under it, and an expression
  // stating none has no standing to take it away: reading it as a request would
  // leave a region read under a value nothing wrote while the text plainly
  // wrote one.
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

// §22.11.1: a keyword stands at its default exactly when it has no entry, so
// dropping the entries the directives wrote leaves every keyword at the value
// it had before any text was read.
void ProtectKeywordScope::Reset() { in_effect_.clear(); }

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

// §34.5.16 settles this the same way and from the same place: a digest_keyowner
// a directive named stands as it was written, and where the text named none
// there is still an entity whose key the digest is under -- the one whose key
// the data are under -- so that name fills the place rather than nothing at
// all. What fills it is a default, and it is reported as one.
//
// It is the value that name has where the reading stands rather than where the
// digest's own keyword was passed over, §34.4 making the scope of both lexical:
// "current" is what the text has in effect at this point, so a text naming one
// provider for one region and another for the next fills each region's digest
// from the name standing beside it.
//
// What decides between the two is whether an entity was specified, not whether
// the keyword was mentioned: the keyword written with nothing against it named
// no entity any more than leaving it out did, so the same value fills the place
// either way.
ProtectKeywordValue ProtectKeywordScope::DigestKeyownerInEffect() const {
  ProtectKeywordValue written = ValueOf(kDigestKeyownerKeyword);
  if (!written.defaulted && !written.value.empty()) return written;
  return {ValueOf(kDataKeyownerKeyword).value, true};
}

// §34.5.19 settles this the same way and from the same place: a public key a
// directive designated for the digest stands as it was written, and where the
// text designated none there is still a public key the digest's key may be
// reached through -- the one the region's data are under -- so that value fills
// the place rather than nothing at all. What fills it is a default, and it is
// reported as one.
//
// It is the value that designation has where the reading stands rather than
// where the digest's own keyword was passed over, §34.4 making the scope of
// both lexical: "current" is what the text has in effect at this point, so a
// text designating one public key for one region and another for the next
// fills each region's digest from the designation standing beside it.
//
// What decides between the two is whether a public key was specified, not
// whether the keyword was mentioned. §34.5.19.1 writes the keyword standing
// alone, so what specifies a value is the encoded line beneath it: a keyword
// whose line carried nothing designated a key no more than leaving the keyword
// out did, and the same value fills the place either way.
ProtectKeywordValue ProtectKeywordScope::DigestPublicKeyInEffect() const {
  ProtectKeywordValue written = ValueOf(kDigestPublicKeyKeyword);
  if (!written.defaulted && !written.value.empty()) return written;
  return {ValueOf(kDataPublicKeyKeyword).value, true};
}

}  // namespace delta
