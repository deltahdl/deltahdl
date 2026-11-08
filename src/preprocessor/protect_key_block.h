#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"

namespace delta {

inline constexpr std::string_view kKeyBlockKeyword = "key_block";

std::string ProtectDataDecryptKeyDirective(std::string_view encoded_key);

struct ProtectDataDecryption {
  std::string decrypt_key;
  std::string method;
  std::string keyname;
  std::string keyowner;
  std::string stated_keyowner;
  std::string public_key;
};

bool SameProtectDataDecryption(const ProtectDataDecryption& a,
                               const ProtectDataDecryption& b);

struct ProtectKeyBlockRequest {
  std::string keyowner;
  std::string stated_keyowner;
  std::string keyname;
  std::string public_key;
  ProtectDataDecryption data;
  uint32_t line = 0;
};

class ProtectKeyBlockRequests {
 public:
  void Designate(std::string_view keyowner, std::string_view keyname,
                 const ProtectDataDecryption& data, uint32_t line);

  void DesignatePublicKey(std::string_view keyowner, std::string_view key,
                          const ProtectDataDecryption& data, uint32_t line);

  void UseKeyMethod(std::string_view method) { key_method_ = method; }
  std::string_view KeyMethod() const { return key_method_; }

  const std::vector<ProtectKeyBlockRequest>& Requests() const {
    return requests_;
  }
  bool Empty() const { return requests_.empty(); }

 private:
  std::vector<ProtectKeyBlockRequest> requests_;
  std::string key_method_;
};

struct ProtectKeyBlocks {
  std::string data_key;
  std::string digest_key;
  std::string directives;
  uint32_t data_changed_line = 0;
};

std::string ProtectGeneratedDataKey(std::string_view cleartext,
                                    std::string_view under);

std::string ProtectKeyBlockContent(const ProtectDataDecryption& data,
                                   const ProtectDigestDecryption& digest,
                                   const ProtectEncoding& encoding);

std::string ProtectKeyBlockDirectives(const ProtectKeyBlockRequest& request,
                                      std::string_view content,
                                      std::string_view key,
                                      const ProtectEnvelopeEncodings& encodings,
                                      std::string_view method);

struct ProtectKeyBlockRegion {
  std::string_view cleartext;
  std::string_view data_key;
  std::string_view digest_key;
};

ProtectKeyBlocks ProtectKeyBlocksFor(const ProtectKeyBlockRequests& requests,
                                     const ProtectKeyBlockRegion& region,
                                     const ProtectKeyList& keys,
                                     const ProtectEnvelopeEncodings& encodings,
                                     const ProtectDigestBlockPolicy& digest);

}  // namespace delta
