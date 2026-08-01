#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_processing.h"

namespace delta {
namespace {

// An encrypted region records a fingerprint of its own text ahead of the text
// itself. Recovering that fingerprint is how the decrypting half tells the key
// the region was encrypted under from any other key it might be given: a
// different key yields different bytes throughout, and the fingerprint they
// carry no longer describes the text beside it.
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

uint32_t ReadFingerprintPrefix(std::string_view bytes) {
  uint32_t fingerprint = 0;
  for (size_t n = 0; n < kFingerprintBytes; ++n) {
    auto byte = static_cast<uint8_t>(bytes[n]);
    fingerprint = (fingerprint << 8) | byte;
  }
  return fingerprint;
}

// The keyed step of both halves. Combining the bytes with the key twice gives
// the bytes back, which is what makes one key both encrypt and decrypt a
// region.
std::string CombineWithKey(std::string_view bytes, std::string_view key) {
  std::string combined;
  combined.reserve(bytes.size());
  for (size_t n = 0; n < bytes.size(); ++n) {
    auto byte = static_cast<uint8_t>(bytes[n]);
    auto key_byte = static_cast<uint8_t>(key[n % key.size()]);
    combined.push_back(static_cast<char>(byte ^ key_byte));
  }
  return combined;
}

}  // namespace

// The block a region is recorded in is written as text by §34.5.9's coding
// schemes, which are spelled out in protect_encoding.h. Which scheme is used is
// what a text's encoding pragma expression settles, so the writing and the
// reading of a block are given a scheme rather than holding one of their own.

size_t ProtectedRegionBlockSize(std::string_view cleartext) {
  return kFingerprintBytes + cleartext.size();
}

std::string EncryptProtectedRegion(std::string_view cleartext,
                                   std::string_view key,
                                   std::string_view enctype) {
  if (key.empty()) return "";
  std::string blob = FingerprintPrefix(FingerprintOf(cleartext));
  blob.append(cleartext);
  ProtectEncoding encoding;
  encoding.enctype = std::string(enctype);
  return EncodeProtectBlock(CombineWithKey(blob, key), encoding);
}

bool DecryptProtectedBlock(std::string_view block, std::string_view key,
                           std::string* cleartext) {
  if (key.empty()) return false;
  if (block.size() < kFingerprintBytes) return false;
  std::string recovered = CombineWithKey(block, key);
  std::string_view text = std::string_view(recovered).substr(kFingerprintBytes);
  if (FingerprintOf(text) != ReadFingerprintPrefix(recovered)) return false;
  cleartext->assign(text);
  return true;
}

bool DecryptProtectedRegion(std::string_view data_block, std::string_view key,
                            std::string* cleartext, std::string_view enctype) {
  std::string block;
  if (!DecodeProtectBlock(data_block, enctype, &block)) return false;
  return DecryptProtectedBlock(block, key, cleartext);
}

}  // namespace delta
