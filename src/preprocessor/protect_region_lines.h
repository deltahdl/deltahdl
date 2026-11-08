#pragma once

#include <cstdint>
#include <deque>
#include <memory>
#include <string>
#include <string_view>
#include <utility>

#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_key_block.h"

namespace delta {

struct RegionKeyReader {
  std::shared_ptr<std::deque<std::string>> held_lines =
      std::make_shared<std::deque<std::string>>();
  std::string_view Hold(std::string text) {
    held_lines->push_back(std::move(text));
    return held_lines->back();
  }

  RegionKeyNames names;
  std::string_view author;
  std::string_view author_info;
  std::string comment_directives;
  std::string_view digest_method;
  uint32_t digest_method_line = 0;
  std::string_view digest_key_method;
  bool digest_requested = false;
  std::string_view key_method;
  uint32_t key_method_line = 0;
  uint32_t data_keyname_line = 0;
  uint32_t digest_keyname_line = 0;
  uint32_t key_keyname_line = 0;
  std::string_view data_method;
  uint32_t data_method_line = 0;
  ProtectEncoding encoding = DefaultProtectEncoding();
  ProtectKeyBlockRequests key_blocks;
  bool encoded_key_next = false;
  bool encoded_data_key_next = false;
  bool encoded_digest_key_next = false;
  bool encoded_data_decrypt_key_next = false;
  bool encoded_digest_decrypt_key_next = false;
  std::string data_decrypt_key;
  std::string digest_decrypt_key;
};

ProtectDataDecryption DataDecryptionInEffect(const RegionKeyNames& names,
                                             std::string_view method = {});

void TakeKeyNamesOutsideProtectedBlock(std::string_view line, uint32_t line_num,
                                       bool contained, RegionKeyReader* reader);

}  // namespace delta
