#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_processing.h"

namespace delta {
namespace {

// An encrypted region records a fingerprint of its own text ahead of the text
// itself. Recovering that fingerprint is how the decrypting half tells the key
// the region was encrypted under from any other key it might be given: a
// different key yields different bytes throughout, and the fingerprint they
// carry no longer describes the text beside it.
//
// "Throughout" is what KeyStream below is for. It held only of two keys
// differing within the block's length while the bytes were combined with the
// key's own characters, and #3274 is the defect that left.
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

// One run of the value the key is combined with, of the length `wanted`.
//
// Every byte of it depends on every character of the key. A run taken from the
// key's own characters would depend on only as many of them as the run is long,
// and two keys agreeing over that many characters would then produce the same
// run: a block encrypted under one would open under the other, and the
// fingerprint beside it would describe the text it recovered to. A digest block
// is kFingerprintBytes plus a 20-byte digest, so 24 characters of a key would
// have decided whether a digest sealed under some other key was accepted.
//
// The run is the digests of the key with a counter written after it, taken one
// after another until it is long enough. A digest is a value in which a change
// anywhere in the input changes the whole output, so a key differing at any one
// character gives a different run from its first byte. The counter is what
// makes the runs differ from each other, a run repeating itself being one in
// which a block's own bytes could be read off against each other.
std::string KeyStream(std::string_view key, size_t wanted) {
  std::string stream;
  stream.reserve(wanted);
  for (uint32_t counter = 0; stream.size() < wanted; ++counter) {
    std::string input(key);
    for (size_t n = 4; n > 0; --n) {
      input.push_back(static_cast<char>((counter >> ((n - 1) * 8)) & 0xFFU));
    }
    std::string digest;
    // The identifier is this file's own choice rather than the one a text
    // named. §34.5.21's identifier says what the digests written into an
    // envelope are computed with, which is a thing a reader is told; this is
    // the cipher's internal step and no envelope states it, so it is fixed
    // here and both halves reach it through the same call.
    if (!ProtectMessageDigest(input, kSha1DigestMethod, &digest)) return stream;
    stream.append(digest);
  }
  stream.resize(wanted);
  return stream;
}

// The keyed step of both halves. Combining the bytes with the key twice gives
// the bytes back, which is what makes one key both encrypt and decrypt a
// region.
std::string CombineWithKey(std::string_view bytes, std::string_view key) {
  std::string stream = KeyStream(key, bytes.size());
  // A key the digest could not be taken of leaves a run shorter than the bytes
  // it is to be combined with, and combining what there is would leave the rest
  // of a region in the clear. There is no such key today -- kSha1DigestMethod
  // is one this implementation provides -- and the check is here so that a
  // change to the digests available cannot quietly stop encrypting.
  if (stream.size() != bytes.size()) return "";
  std::string combined;
  combined.reserve(bytes.size());
  for (size_t n = 0; n < bytes.size(); ++n) {
    auto byte = static_cast<uint8_t>(bytes[n]);
    auto stream_byte = static_cast<uint8_t>(stream[n]);
    combined.push_back(static_cast<char>(byte ^ stream_byte));
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
  std::string combined = CombineWithKey(blob, key);
  // CombineWithKey leaves nothing where it could not produce a run as long as
  // the bytes, and an empty block written out would be a region whose text went
  // nowhere rather than a region that was sealed.
  if (combined.size() != blob.size()) return "";
  ProtectEncoding encoding;
  encoding.enctype = std::string(enctype);
  return EncodeProtectBlock(combined, encoding);
}

bool DecryptProtectedBlock(std::string_view block, std::string_view key,
                           std::string* cleartext) {
  if (key.empty()) return false;
  if (block.size() < kFingerprintBytes) return false;
  std::string recovered = CombineWithKey(block, key);
  if (recovered.size() != block.size()) return false;
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
