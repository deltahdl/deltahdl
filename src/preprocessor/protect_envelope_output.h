#pragma once

#include <string>
#include <string_view>

#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_key_block.h"
#include "preprocessor/protect_keywords.h"

namespace delta {

inline constexpr std::string_view kEncryptAgent = "deltahdl";

inline constexpr std::string_view kEncryptAgentInfo =
    "SystemVerilog elaborator and protect envelope writer";

inline constexpr std::string_view kDataMethod = "x-deltahdl-stream";

struct RegionKeyNames {
  std::string_view data_keyname;
  std::string_view data_keyowner;
  std::string data_public_key;
  std::string_view digest_keyname;
  std::string_view digest_keyowner;
  std::string digest_public_key;
  std::string_view key_keyname;
  std::string_view key_keyowner;
  std::string key_public_key;
};

struct EncryptionEnvelope {
  std::string_view begin_directive;
  std::string_view body;
  std::string_view end_directive;
  std::string_view author;
  std::string_view author_info;
  std::string_view comment_directives;
  RegionKeyNames names;
  std::string_view digest_method;
  std::string_view digest_key_method;
  std::string_view key_method;
  std::string_view data_method;
  ProtectEncoding requested_encoding;
};

struct RegionEncryption {
  std::string key;
  ProtectKeyBlocks key_blocks;
  ProtectDigestBlockPolicy digest;
};

std::string_view RegionDigestKey(const RegionKeyNames& names,
                                 const ProtectKeyList& keys);

ProtectEncoding EnvelopeBlockEncoding(const ProtectEncoding& requested);

ProtectEncoding RequestedBlockEncoding(const ProtectEncoding& requested);

ProtectEnvelopeEncodings EnvelopeEncodings(const ProtectEncoding& requested);

std::string DecryptionEnvelopeText(const EncryptionEnvelope& envelope,
                                   const RegionEncryption& how);

}  // namespace delta
