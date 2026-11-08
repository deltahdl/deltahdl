#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "preprocessor/protect_des.h"
#include "preprocessor/protect_digest_algorithms.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_processing.h"

namespace delta {
namespace {

constexpr size_t kFingerprintBytes = 4;
constexpr uint32_t kFingerprintBasis = 0x811C9DC5U;
constexpr uint32_t kFingerprintFactor = 0x01000193U;

uint32_t FingerprintOf(std::string_view text) {
  uint32_t fingerprint = kFingerprintBasis;
  for (char c : text) {
    fingerprint ^= static_cast<uint8_t>(c);
    fingerprint *= kFingerprintFactor;
  }
  return fingerprint;
}

std::string FingerprintPrefix(uint32_t fingerprint) {
  std::string prefix;
  for (size_t n = kFingerprintBytes; n > 0; --n) {
    prefix.push_back(static_cast<char>((fingerprint >> ((n - 1) * 8)) & 0xFFU));
  }
  return prefix;
}

std::string KeyStream(std::string_view key, size_t wanted) {
  std::string stream;
  stream.reserve(wanted);
  for (uint32_t counter = 0; stream.size() < wanted; ++counter) {
    std::string input(key);
    for (size_t n = 4; n > 0; --n) {
      input.push_back(static_cast<char>((counter >> ((n - 1) * 8)) & 0xFFU));
    }
    stream.append(Sha1Digest(input));
  }
  stream.resize(wanted);
  return stream;
}

std::string CombineWithKey(std::string_view bytes, std::string_view key) {
  std::string stream = KeyStream(key, bytes.size());
  std::string combined;
  combined.reserve(bytes.size());
  for (size_t n = 0; n < bytes.size(); ++n) {
    auto byte = static_cast<uint8_t>(bytes[n]);
    auto stream_byte = static_cast<uint8_t>(stream[n]);
    combined.push_back(static_cast<char>(byte ^ stream_byte));
  }
  return combined;
}

std::string DesKeyOf(std::string_view key) {
  return KeyStream(key, kDesKeyBytes);
}

std::string FreshInitializationVector(std::string_view key,
                                      std::string_view cleartext) {
  static uint64_t counter = 0;
  ++counter;
  std::string seed(key);
  seed.append(cleartext);
  for (size_t n = 8; n > 0; --n) {
    seed.push_back(static_cast<char>((counter >> ((n - 1) * 8)) & 0xFFU));
  }
  return KeyStream(seed, kDesBlockBytes);
}

bool UsesDesCbc(std::string_view method) { return method == kDesCbcMethod; }

std::string EncryptedRegionBytes(std::string_view cleartext,
                                 std::string_view key,
                                 std::string_view method) {
  if (!UsesDesCbc(method)) {
    std::string blob = FingerprintPrefix(FingerprintOf(cleartext));
    blob.append(cleartext);
    return CombineWithKey(blob, key);
  }
  std::string iv = FreshInitializationVector(key, cleartext);
  std::string ciphertext = DesCbcEncrypt(cleartext, DesKeyOf(key), iv);
  return iv + ciphertext;
}

bool RecoverDesCbcRegion(std::string_view block, std::string_view key,
                         std::string* cleartext) {
  if (block.size() <= kDesBlockBytes) return false;
  return DesCbcDecrypt(block.substr(kDesBlockBytes), DesKeyOf(key),
                       block.substr(0, kDesBlockBytes), cleartext);
}

}  // namespace

size_t ProtectedRegionBlockSize(std::string_view cleartext,
                                std::string_view method) {
  if (!UsesDesCbc(method)) return kFingerprintBytes + cleartext.size();
  size_t padded =
      cleartext.size() + kDesBlockBytes - (cleartext.size() % kDesBlockBytes);
  return kDesBlockBytes + padded;
}

std::string EncryptProtectedRegion(std::string_view cleartext,
                                   std::string_view key,
                                   std::string_view enctype,
                                   std::string_view method,
                                   size_t line_length) {
  if (key.empty()) return "";
  std::string recorded = EncryptedRegionBytes(cleartext, key, method);
  ProtectEncoding encoding;
  encoding.enctype = std::string(enctype);
  encoding.line_length = line_length;
  return EncodeProtectBlock(recorded, encoding);
}

bool DecryptProtectedBlock(std::string_view block, std::string_view key,
                           std::string* cleartext, std::string_view method) {
  if (key.empty()) return false;
  if (UsesDesCbc(method)) return RecoverDesCbcRegion(block, key, cleartext);
  if (block.size() < kFingerprintBytes) return false;
  std::string recovered = CombineWithKey(block, key);
  std::string_view whole(recovered);
  std::string_view prefix = whole.substr(0, kFingerprintBytes);
  std::string_view text = whole.substr(kFingerprintBytes);
  if (prefix != FingerprintPrefix(FingerprintOf(text))) return false;
  cleartext->assign(text);
  return true;
}

bool DecryptProtectedRegion(std::string_view data_block, std::string_view key,
                            std::string* cleartext, std::string_view enctype,
                            std::string_view method) {
  std::string block;
  if (!DecodeProtectBlock(data_block, enctype, &block)) return false;
  return DecryptProtectedBlock(block, key, cleartext, method);
}

}  // namespace delta
