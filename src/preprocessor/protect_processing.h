#pragma once

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"

namespace delta {

inline constexpr std::string_view kDataBlockKeyword = "data_block";

size_t ProtectedRegionBlockSize(std::string_view cleartext,
                                std::string_view method = {});

std::string EncryptProtectedRegion(std::string_view cleartext,
                                   std::string_view key,
                                   std::string_view enctype = kBlockEnctype,
                                   std::string_view method = {},
                                   size_t line_length = 0);

bool DecryptProtectedBlock(std::string_view block, std::string_view key,
                           std::string* cleartext,
                           std::string_view method = {});

bool DecryptProtectedRegion(std::string_view data_block, std::string_view key,
                            std::string* cleartext,
                            std::string_view enctype = kBlockEnctype,
                            std::string_view method = {});

struct EnvelopeEncryptionState;

class EnvelopeEncryptor {
 public:
  EnvelopeEncryptor(std::string_view exchange_key, const ProtectKeyList& keys,
                    DiagEngine* diag);
  ~EnvelopeEncryptor();
  EnvelopeEncryptor(const EnvelopeEncryptor&) = delete;
  EnvelopeEncryptor& operator=(const EnvelopeEncryptor&) = delete;

  std::string Encrypt(std::string_view source_text, uint32_t file_id);

  std::string Finish();

 private:
  std::unique_ptr<EnvelopeEncryptionState> state_;
};

std::string EncryptEnvelopes(std::string_view source_text,
                             std::string_view exchange_key,
                             const ProtectKeyList& keys = ProtectKeyList(),
                             DiagEngine* diag = nullptr, uint32_t file_id = 0);

}  // namespace delta
