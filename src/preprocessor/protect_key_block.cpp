#include "preprocessor/protect_key_block.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>

#include "preprocessor/protect_digest_algorithms.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

namespace delta {
namespace {

void AppendDirective(std::string& text, std::string_view keyword,
                     std::string_view value) {
  text.append("`pragma protect ").append(keyword).append("=\"");
  text.append(value).append("\"\n");
}

std::string_view KeyOfRequest(const ProtectKeyBlockRequest& request,
                              const ProtectKeyList& keys) {
  std::string_view under_name = keys.KeyFor(request.keyowner, request.keyname);
  if (!under_name.empty()) return under_name;
  return keys.KeyFor(request.keyowner, request.public_key);
}

std::string KeyBlockContentFor(const ProtectKeyBlockRequest& request,
                               const ProtectKeyBlocks& blocks,
                               const ProtectDigestBlockPolicy& digest,
                               const ProtectEncoding& encoding) {
  ProtectDataDecryption data = request.data;
  data.decrypt_key = blocks.data_key;
  ProtectDigestDecryption digest_keys;
  digest_keys.key_method = digest.key_method;
  digest_keys.keyname = digest.keyname;
  digest_keys.digest_method = digest.stated_method;
  if (digest.requested) digest_keys.decrypt_key = blocks.digest_key;
  return ProtectKeyBlockContent(data, digest_keys, encoding);
}

}  // namespace

std::string ProtectDataDecryptKeyDirective(std::string_view encoded_key) {
  std::string text;
  text.append("`pragma protect ").append(kDataDecryptKeyKeyword).append("\n");
  text.append(encoded_key).append("\n");
  return text;
}

void ProtectKeyBlockRequests::Designate(std::string_view keyowner,
                                        std::string_view keyname,
                                        const ProtectDataDecryption& data,
                                        uint32_t line) {
  ProtectKeyBlockRequest request;
  request.keyowner = ProtectPragmaValueBody(keyowner);
  request.stated_keyowner = keyowner;
  request.keyname = ProtectPragmaValueBody(keyname);
  request.data = data;
  request.line = line;
  requests_.push_back(std::move(request));
}

void ProtectKeyBlockRequests::DesignatePublicKey(
    std::string_view keyowner, std::string_view key,
    const ProtectDataDecryption& data, uint32_t line) {
  ProtectKeyBlockRequest request;
  request.keyowner = ProtectPragmaValueBody(keyowner);
  request.stated_keyowner = keyowner;
  request.public_key = key;
  request.data = data;
  request.line = line;
  requests_.push_back(std::move(request));
}

std::string ProtectGeneratedDataKey(std::string_view cleartext,
                                    std::string_view under) {
  std::string material(under);
  material.append(cleartext);
  return Sha1Digest(material);
}

std::string ProtectKeyBlockContent(const ProtectDataDecryption& data,
                                   const ProtectDigestDecryption& digest,
                                   const ProtectEncoding& encoding) {
  std::string text;
  if (!data.stated_keyowner.empty()) {
    text.append(ProtectDataKeyownerDirective(data.stated_keyowner));
  }
  AppendDirective(text, kDataMethodKeyword, data.method);
  if (!data.keyname.empty()) {
    text.append(ProtectDataKeynameDirective(data.keyname));
  }
  text.append(ProtectEncodedValueDirective(encoding, data.decrypt_key.size()));
  text.append(ProtectDataDecryptKeyDirective(
      EncodeProtectValue(data.decrypt_key, encoding)));
  text.append(ProtectDigestDecryptionContent(digest, encoding));
  return text;
}

bool SameProtectDataDecryption(const ProtectDataDecryption& a,
                               const ProtectDataDecryption& b) {
  return a.method == b.method && a.keyname == b.keyname &&
         a.keyowner == b.keyowner && a.public_key == b.public_key;
}

std::string ProtectKeyBlockDirectives(const ProtectKeyBlockRequest& request,
                                      std::string_view content,
                                      std::string_view key,
                                      const ProtectEnvelopeEncodings& encodings,
                                      std::string_view method) {
  std::string text;
  text.append(ProtectKeyKeyownerDirective(request.stated_keyowner));
  if (!request.keyname.empty()) {
    AppendDirective(text, kKeyKeynameKeyword, request.keyname);
  } else {
    text.append(ProtectEncodedValueDirective(encodings.one_line,
                                             request.public_key.size()));
    text.append(ProtectKeyPublicKeyDirective(
        EncodeProtectValue(request.public_key, encodings.one_line)));
  }
  text.append(ProtectEncodedValueDirective(
      encodings.blocks, ProtectedRegionBlockSize(content, method)));
  text.append("`pragma protect ").append(kKeyBlockKeyword).append("\n");
  text.append(
      EncryptProtectedRegion(content, key, encodings.blocks.enctype, method));
  text.push_back('\n');
  return text;
}

ProtectKeyBlocks ProtectKeyBlocksFor(const ProtectKeyBlockRequests& requests,
                                     const ProtectKeyBlockRegion& region,
                                     const ProtectKeyList& keys,
                                     const ProtectEnvelopeEncodings& encodings,
                                     const ProtectDigestBlockPolicy& digest) {
  ProtectKeyBlocks blocks;
  const ProtectDataDecryption* first = nullptr;
  for (const ProtectKeyBlockRequest& request : requests.Requests()) {
    std::string_view key = KeyOfRequest(request, keys);
    if (key.empty()) continue;
    if (blocks.data_key.empty()) {
      blocks.data_key = region.data_key.empty()
                            ? ProtectGeneratedDataKey(region.cleartext, key)
                            : std::string(region.data_key);
      blocks.digest_key = region.digest_key.empty()
                              ? blocks.data_key
                              : std::string(region.digest_key);
    }
    if (first == nullptr) {
      first = &request.data;
    } else if (!SameProtectDataDecryption(*first, request.data) &&
               blocks.data_changed_line == 0) {
      blocks.data_changed_line = request.line;
    }
    std::string content =
        KeyBlockContentFor(request, blocks, digest, encodings.one_line);
    blocks.directives.append(ProtectKeyBlockDirectives(
        request, content, key, encodings, requests.KeyMethod()));
    ProtectDigestBlockPolicy block_digest = digest;
    block_digest.key = blocks.digest_key;
    blocks.directives.append(
        ProtectDigestBlockDirectives(content, block_digest, encodings.blocks));
  }
  return blocks;
}

}  // namespace delta
