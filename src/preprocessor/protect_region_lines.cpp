#include "preprocessor/protect_region_lines.h"

#include <cstdint>
#include <deque>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <utility>

#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_key_block.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_pragma_line.h"

namespace delta {

ProtectDataDecryption DataDecryptionInEffect(const RegionKeyNames& names,
                                             std::string_view method) {
  ProtectDataDecryption data;
  data.method =
      method == kDesCbcMethod ? std::string(method) : std::string(kDataMethod);
  data.keyname = ProtectPragmaValueBody(names.data_keyname);
  data.keyowner = ProtectPragmaValueBody(names.data_keyowner);
  data.stated_keyowner = std::string(names.data_keyowner);
  data.public_key = names.data_public_key;
  return data;
}

namespace {

void TakeMethodKeywords(std::string_view line, uint32_t line_num,
                        RegionKeyReader* reader) {
  std::string_view data_method =
      KeywordSingleValueOnLine(line, kDataMethodKeyword);
  if (!data_method.empty()) {
    reader->data_method = data_method;
    reader->data_method_line = line_num;
  }
  std::string_view digest_method =
      KeywordSingleValueOnLine(line, kDigestMethodKeyword);
  if (!digest_method.empty()) {
    reader->digest_method = digest_method;
    reader->digest_method_line = line_num;
  }
  std::string_view digest_key_method =
      KeywordSingleValueOnLine(line, kDigestKeyMethodKeyword);
  if (!digest_key_method.empty()) reader->digest_key_method = digest_key_method;
  std::string_view key_method =
      KeywordSingleValueOnLine(line, kKeyMethodKeyword);
  if (!key_method.empty()) {
    reader->key_method = key_method;
    reader->key_method_line = line_num;
  }
}

void TakeKeyPublicKeyLine(std::string_view line, uint32_t line_num,
                          RegionKeyReader* reader) {
  reader->encoded_key_next = false;
  std::string key;
  if (ReadProtectEncodedValue(TrimTrailing(TrimLeading(line)), reader->encoding,
                              &key) != ProtectEncodedValueRead::kRead) {
    return;
  }
  reader->names.key_public_key = std::move(key);
  reader->key_blocks.DesignatePublicKey(
      reader->names.key_keyowner, reader->names.key_public_key,
      DataDecryptionInEffect(reader->names,
                             ProtectPragmaValueBody(reader->data_method)),
      line_num);
}

void TakeDataPublicKeyLine(std::string_view line, RegionKeyReader* reader) {
  reader->encoded_data_key_next = false;
  std::string key;
  if (ReadProtectEncodedValue(TrimTrailing(TrimLeading(line)), reader->encoding,
                              &key) != ProtectEncodedValueRead::kRead) {
    return;
  }
  reader->names.data_public_key = std::move(key);
}

void TakeDigestPublicKeyLine(std::string_view line, RegionKeyReader* reader) {
  reader->encoded_digest_key_next = false;
  std::string key;
  if (ReadProtectEncodedValue(TrimTrailing(TrimLeading(line)), reader->encoding,
                              &key) != ProtectEncodedValueRead::kRead) {
    return;
  }
  reader->names.digest_public_key = std::move(key);
}

void TakeEncodingKeyword(std::string_view line, RegionKeyReader* reader) {
  std::string_view written = KeywordValueOnLine(line, kEncodingKeyword);
  if (written.empty()) return;
  ProtectEncoding stated = ParseProtectEncoding(written);
  if (stated.enctype.empty()) return;
  reader->encoding = stated;
}

void TakeEncodedKeyLine(std::string_view line, const ProtectEncoding& encoding,
                        std::string* key) {
  std::string read;
  if (ReadProtectEncodedValue(TrimTrailing(TrimLeading(line)), encoding,
                              &read) == ProtectEncodedValueRead::kRead) {
    *key = std::move(read);
  }
}

bool TookAwaitedPublicKey(std::string_view line, uint32_t line_num,
                          RegionKeyReader* reader) {
  if (reader->encoded_key_next) {
    TakeKeyPublicKeyLine(line, line_num, reader);
    return true;
  }
  if (reader->encoded_data_key_next) {
    TakeDataPublicKeyLine(line, reader);
    return true;
  }
  if (reader->encoded_digest_key_next) {
    TakeDigestPublicKeyLine(line, reader);
    return true;
  }
  if (reader->encoded_data_decrypt_key_next) {
    reader->encoded_data_decrypt_key_next = false;
    TakeEncodedKeyLine(line, reader->encoding, &reader->data_decrypt_key);
    return true;
  }
  if (reader->encoded_digest_decrypt_key_next) {
    reader->encoded_digest_decrypt_key_next = false;
    TakeEncodedKeyLine(line, reader->encoding, &reader->digest_decrypt_key);
    return true;
  }
  return false;
}

void TakeAuthorship(std::string_view line, RegionKeyReader* reader) {
  std::string_view author = KeywordSingleValueOnLine(line, kAuthorKeyword);
  if (!author.empty()) reader->author = author;
  std::string_view author_info =
      KeywordSingleValueOnLine(line, kAuthorInfoKeyword);
  if (!author_info.empty()) reader->author_info = author_info;
  TakeEncodingKeyword(line, reader);
}

void TakeComment(std::string_view line, RegionKeyReader* reader) {
  std::string_view comment = KeywordSingleValueOnLine(line, kCommentKeyword);
  if (comment.empty()) return;
  reader->comment_directives.append(ProtectCommentDirective(comment));
}

void TakeReset(RegionKeyReader* reader) {
  std::string documented = std::move(reader->comment_directives);
  std::shared_ptr<std::deque<std::string>> held = std::move(reader->held_lines);
  *reader = {};
  reader->comment_directives = std::move(documented);
  reader->held_lines = std::move(held);
}

void TakeKeyDesignations(std::string_view line, uint32_t line_num,
                         RegionKeyReader* reader) {
  RegionKeyNames* names = &reader->names;
  std::string_view keyname =
      KeywordSingleValueOnLine(line, kDataKeynameKeyword);
  if (!keyname.empty()) {
    names->data_keyname = keyname;
    reader->data_keyname_line = line_num;
  }
  std::string_view keyowner =
      KeywordSingleValueOnLine(line, kDataKeyownerKeyword);
  if (!keyowner.empty()) names->data_keyowner = keyowner;
  std::string_view digest =
      KeywordSingleValueOnLine(line, kDigestKeynameKeyword);
  if (!digest.empty()) {
    names->digest_keyname = digest;
    reader->digest_keyname_line = line_num;
  }
  std::string_view provider =
      KeywordSingleValueOnLine(line, kDigestKeyownerKeyword);
  if (!provider.empty()) names->digest_keyowner = provider;
  std::string_view key_name =
      KeywordSingleValueOnLine(line, kKeyKeynameKeyword);
  std::string_view key_owner =
      KeywordSingleValueOnLine(line, kKeyKeyownerKeyword);
  if (!key_owner.empty()) names->key_keyowner = key_owner;
  if (!key_name.empty()) {
    names->key_keyname = key_name;
    reader->key_keyname_line = line_num;
    reader->key_blocks.Designate(
        names->key_keyowner, key_name,
        DataDecryptionInEffect(*names,
                               ProtectPragmaValueBody(reader->data_method)),
        line_num);
  }
}

void TakeAnnouncements(std::string_view line, RegionKeyReader* reader) {
  if (NamesKeyword(line, kDigestBlockKeyword)) reader->digest_requested = true;
  reader->encoded_data_decrypt_key_next =
      NamesBareKeyword(line, kDataDecryptKeyKeyword);
  reader->encoded_digest_decrypt_key_next =
      NamesBareKeyword(line, kDigestDecryptKeyKeyword);
  reader->encoded_key_next = NamesBareKeyword(line, kKeyPublicKeyKeyword);
  reader->encoded_data_key_next = NamesBareKeyword(line, kDataPublicKeyKeyword);
  reader->encoded_digest_key_next =
      NamesBareKeyword(line, kDigestPublicKeyKeyword);
}

void TakeKeyNames(std::string_view line, uint32_t line_num,
                  RegionKeyReader* reader) {
  if (TookAwaitedPublicKey(line, line_num, reader)) return;
  TakeComment(line, reader);
  if (ResetsProtectPragmaLine(line)) {
    TakeReset(reader);
    return;
  }
  std::optional<std::string> after_reset = ProtectLineAfterLastReset(line);
  if (after_reset.has_value()) TakeReset(reader);
  std::string_view read =
      after_reset.has_value() ? reader->Hold(std::move(*after_reset)) : line;
  TakeAuthorship(read, reader);
  TakeKeyDesignations(read, line_num, reader);
  TakeMethodKeywords(read, line_num, reader);
  TakeAnnouncements(read, reader);
}

}  // namespace

void TakeKeyNamesOutsideProtectedBlock(std::string_view line, uint32_t line_num,
                                       bool contained,
                                       RegionKeyReader* reader) {
  if (!contained) {
    TakeKeyNames(line, line_num, reader);
    return;
  }
  reader->encoded_key_next = false;
  reader->encoded_data_key_next = false;
  reader->encoded_digest_key_next = false;
}

}  // namespace delta
