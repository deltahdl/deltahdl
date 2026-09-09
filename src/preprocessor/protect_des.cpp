#include "preprocessor/protect_des.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

namespace delta {
namespace {

// FIPS 46-3 numbers the bits of a block from 1 at the left, so a table entry is
// a position counted from the most significant bit of the value it selects
// from. `width` is how many bits of `src` are significant, and the answer is
// `count` bits wide with the first entry landing in its most significant bit.
uint64_t Permute(uint64_t src, unsigned width, const uint8_t* table,
                 unsigned count) {
  uint64_t out = 0;
  for (unsigned i = 0; i < count; ++i) {
    uint64_t bit = (src >> (width - table[i])) & 1ULL;
    out |= bit << (count - 1 - i);
  }
  return out;
}

// The initial permutation and its inverse, applied to the block on the way in
// and on the way out.
constexpr uint8_t kInitialPermutation[64] = {
    58, 50, 42, 34, 26, 18, 10, 2, 60, 52, 44, 36, 28, 20, 12, 4,
    62, 54, 46, 38, 30, 22, 14, 6, 64, 56, 48, 40, 32, 24, 16, 8,
    57, 49, 41, 33, 25, 17, 9,  1, 59, 51, 43, 35, 27, 19, 11, 3,
    61, 53, 45, 37, 29, 21, 13, 5, 63, 55, 47, 39, 31, 23, 15, 7};

constexpr uint8_t kFinalPermutation[64] = {
    40, 8, 48, 16, 56, 24, 64, 32, 39, 7, 47, 15, 55, 23, 63, 31,
    38, 6, 46, 14, 54, 22, 62, 30, 37, 5, 45, 13, 53, 21, 61, 29,
    36, 4, 44, 12, 52, 20, 60, 28, 35, 3, 43, 11, 51, 19, 59, 27,
    34, 2, 42, 10, 50, 18, 58, 26, 33, 1, 41, 9,  49, 17, 57, 25};

// The expansion that takes the right half from 32 bits to the 48 the subkey is
// combined with, and the permutation applied to what the substitution boxes
// leave.
constexpr uint8_t kExpansion[48] = {
    32, 1,  2,  3,  4,  5,  4,  5,  6,  7,  8,  9,  8,  9,  10, 11,
    12, 13, 12, 13, 14, 15, 16, 17, 16, 17, 18, 19, 20, 21, 20, 21,
    22, 23, 24, 25, 24, 25, 26, 27, 28, 29, 28, 29, 30, 31, 32, 1};

constexpr uint8_t kRoundPermutation[32] = {
    16, 7, 20, 21, 29, 12, 28, 17, 1,  15, 23, 26, 5,  18, 31, 10,
    2,  8, 24, 14, 32, 27, 3,  9,  19, 13, 30, 6,  22, 11, 4,  25};

// The two permuted choices of the key schedule. The first drops the parity bit
// of every byte, leaving the 56 bits the algorithm uses; the second selects the
// 48 bits of each round's subkey out of the rotated halves.
constexpr uint8_t kPermutedChoiceOne[56] = {
    57, 49, 41, 33, 25, 17, 9,  1,  58, 50, 42, 34, 26, 18, 10, 2,  59, 51, 43,
    35, 27, 19, 11, 3,  60, 52, 44, 36, 63, 55, 47, 39, 31, 23, 15, 7,  62, 54,
    46, 38, 30, 22, 14, 6,  61, 53, 45, 37, 29, 21, 13, 5,  28, 20, 12, 4};

constexpr uint8_t kPermutedChoiceTwo[48] = {
    14, 17, 11, 24, 1,  5,  3,  28, 15, 6,  21, 10, 23, 19, 12, 4,
    26, 8,  16, 7,  27, 20, 13, 2,  41, 52, 31, 37, 47, 55, 30, 40,
    51, 45, 33, 48, 44, 49, 39, 56, 34, 53, 46, 42, 50, 36, 29, 32};

// How far each round rotates the two halves of the key.
constexpr uint8_t kKeyRotations[16] = {1, 1, 2, 2, 2, 2, 2, 2,
                                       1, 2, 2, 2, 2, 2, 2, 1};

// The eight substitution boxes, each read as four rows of sixteen: the outer
// two bits of a six-bit group select the row and the inner four the column.
constexpr uint8_t kSubstitutionBoxes[8][64] = {
    {14, 4,  13, 1, 2,  15, 11, 8,  3,  10, 6,  12, 5,  9,  0, 7,
     0,  15, 7,  4, 14, 2,  13, 1,  10, 6,  12, 11, 9,  5,  3, 8,
     4,  1,  14, 8, 13, 6,  2,  11, 15, 12, 9,  7,  3,  10, 5, 0,
     15, 12, 8,  2, 4,  9,  1,  7,  5,  11, 3,  14, 10, 0,  6, 13},
    {15, 1,  8,  14, 6,  11, 3,  4,  9,  7, 2,  13, 12, 0, 5,  10,
     3,  13, 4,  7,  15, 2,  8,  14, 12, 0, 1,  10, 6,  9, 11, 5,
     0,  14, 7,  11, 10, 4,  13, 1,  5,  8, 12, 6,  9,  3, 2,  15,
     13, 8,  10, 1,  3,  15, 4,  2,  11, 6, 7,  12, 0,  5, 14, 9},
    {10, 0,  9,  14, 6, 3,  15, 5,  1,  13, 12, 7,  11, 4,  2,  8,
     13, 7,  0,  9,  3, 4,  6,  10, 2,  8,  5,  14, 12, 11, 15, 1,
     13, 6,  4,  9,  8, 15, 3,  0,  11, 1,  2,  12, 5,  10, 14, 7,
     1,  10, 13, 0,  6, 9,  8,  7,  4,  15, 14, 3,  11, 5,  2,  12},
    {7,  13, 14, 3, 0,  6,  9,  10, 1,  2, 8, 5,  11, 12, 4,  15,
     13, 8,  11, 5, 6,  15, 0,  3,  4,  7, 2, 12, 1,  10, 14, 9,
     10, 6,  9,  0, 12, 11, 7,  13, 15, 1, 3, 14, 5,  2,  8,  4,
     3,  15, 0,  6, 10, 1,  13, 8,  9,  4, 5, 11, 12, 7,  2,  14},
    {2,  12, 4,  1,  7,  10, 11, 6,  8,  5,  3,  15, 13, 0, 14, 9,
     14, 11, 2,  12, 4,  7,  13, 1,  5,  0,  15, 10, 3,  9, 8,  6,
     4,  2,  1,  11, 10, 13, 7,  8,  15, 9,  12, 5,  6,  3, 0,  14,
     11, 8,  12, 7,  1,  14, 2,  13, 6,  15, 0,  9,  10, 4, 5,  3},
    {12, 1,  10, 15, 9, 2,  6,  8,  0,  13, 3,  4,  14, 7,  5,  11,
     10, 15, 4,  2,  7, 12, 9,  5,  6,  1,  13, 14, 0,  11, 3,  8,
     9,  14, 15, 5,  2, 8,  12, 3,  7,  0,  4,  10, 1,  13, 11, 6,
     4,  3,  2,  12, 9, 5,  15, 10, 11, 14, 1,  7,  6,  0,  8,  13},
    {4,  11, 2,  14, 15, 0, 8,  13, 3,  12, 9, 7,  5,  10, 6, 1,
     13, 0,  11, 7,  4,  9, 1,  10, 14, 3,  5, 12, 2,  15, 8, 6,
     1,  4,  11, 13, 12, 3, 7,  14, 10, 15, 6, 8,  0,  5,  9, 2,
     6,  11, 13, 8,  1,  4, 10, 7,  9,  5,  0, 15, 14, 2,  3, 12},
    {13, 2,  8,  4, 6,  15, 11, 1,  10, 9,  3,  14, 5,  0,  12, 7,
     1,  15, 13, 8, 10, 3,  7,  4,  12, 5,  6,  11, 0,  14, 9,  2,
     7,  11, 4,  1, 9,  12, 14, 2,  0,  6,  10, 13, 15, 3,  5,  8,
     2,  1,  14, 7, 4,  10, 8,  13, 15, 12, 9,  0,  3,  5,  6,  11}};

// The sixteen subkeys, in the order encryption applies them.
void KeySchedule(uint64_t key, uint64_t subkeys[16]) {
  uint64_t permuted = Permute(key, 64, kPermutedChoiceOne, 56);
  auto left = static_cast<uint32_t>((permuted >> 28) & 0x0FFFFFFFU);
  auto right = static_cast<uint32_t>(permuted & 0x0FFFFFFFU);
  for (unsigned round = 0; round < 16; ++round) {
    unsigned by = kKeyRotations[round];
    left = ((left << by) | (left >> (28 - by))) & 0x0FFFFFFFU;
    right = ((right << by) | (right >> (28 - by))) & 0x0FFFFFFFU;
    uint64_t joined = (static_cast<uint64_t>(left) << 28) | right;
    subkeys[round] = Permute(joined, 56, kPermutedChoiceTwo, 48);
  }
}

// The round function: the right half expanded to 48 bits, combined with the
// subkey, put through the substitution boxes six bits at a time and permuted.
uint32_t RoundFunction(uint32_t half, uint64_t subkey) {
  uint64_t expanded = Permute(half, 32, kExpansion, 48) ^ subkey;
  uint32_t substituted = 0;
  for (unsigned box = 0; box < 8; ++box) {
    auto group = static_cast<unsigned>((expanded >> (42 - 6 * box)) & 0x3FU);
    unsigned row = ((group >> 4) & 0x2U) | (group & 0x1U);
    unsigned column = (group >> 1) & 0xFU;
    substituted =
        (substituted << 4) | kSubstitutionBoxes[box][row * 16 + column];
  }
  return static_cast<uint32_t>(Permute(substituted, 32, kRoundPermutation, 32));
}

// The sixteen rounds over one block, the subkeys applied in the order given.
// FIPS 46-3 leaves the halves swapped after the last round, which is why the
// preoutput is assembled right half first.
uint64_t DesRounds(uint64_t block, const uint64_t subkeys[16], bool reversed) {
  uint64_t permuted = Permute(block, 64, kInitialPermutation, 64);
  auto left = static_cast<uint32_t>(permuted >> 32);
  auto right = static_cast<uint32_t>(permuted & 0xFFFFFFFFU);
  for (unsigned round = 0; round < 16; ++round) {
    uint32_t next =
        left ^ RoundFunction(right, subkeys[reversed ? 15 - round : round]);
    left = right;
    right = next;
  }
  uint64_t preoutput = (static_cast<uint64_t>(right) << 32) | left;
  return Permute(preoutput, 64, kFinalPermutation, 64);
}

// Eight bytes read as one 64-bit value, the first byte holding bits 1 to 8,
// and the inverse of that reading.
uint64_t WordOfBytes(std::string_view bytes) {
  uint64_t value = 0;
  for (char c : bytes) {
    value = (value << 8) | static_cast<uint8_t>(c);
  }
  return value;
}

std::string BytesOfWord(uint64_t value) {
  std::string bytes;
  for (size_t n = kDesBlockBytes; n > 0; --n) {
    bytes.push_back(static_cast<char>((value >> ((n - 1) * 8)) & 0xFFU));
  }
  return bytes;
}

std::string OneBlock(std::string_view block, std::string_view key,
                     bool reversed) {
  if (block.size() != kDesBlockBytes || key.size() != kDesKeyBytes) return "";
  uint64_t subkeys[16] = {};
  KeySchedule(WordOfBytes(key), subkeys);
  return BytesOfWord(DesRounds(WordOfBytes(block), subkeys, reversed));
}

// The two blocks combined byte by byte, which is what chains one block of CBC
// to the one before it.
std::string CombineBlocks(std::string_view left, std::string_view right) {
  std::string combined;
  combined.reserve(left.size());
  for (size_t n = 0; n < left.size(); ++n) {
    combined.push_back(static_cast<char>(static_cast<uint8_t>(left[n]) ^
                                         static_cast<uint8_t>(right[n])));
  }
  return combined;
}

}  // namespace

std::string DesEncryptBlock(std::string_view block, std::string_view key) {
  return OneBlock(block, key, /*reversed=*/false);
}

std::string DesDecryptBlock(std::string_view block, std::string_view key) {
  return OneBlock(block, key, /*reversed=*/true);
}

std::string DesCbcEncrypt(std::string_view cleartext, std::string_view key,
                          std::string_view iv) {
  if (key.size() != kDesKeyBytes || iv.size() != kDesBlockBytes) return "";
  std::string padded(cleartext);
  size_t pad = kDesBlockBytes - (padded.size() % kDesBlockBytes);
  padded.append(pad, static_cast<char>(pad));
  std::string chain(iv);
  std::string ciphertext;
  ciphertext.reserve(padded.size());
  for (size_t at = 0; at < padded.size(); at += kDesBlockBytes) {
    std::string_view block(padded);
    block = block.substr(at, kDesBlockBytes);
    chain = DesEncryptBlock(CombineBlocks(block, chain), key);
    if (chain.size() != kDesBlockBytes) return "";
    ciphertext.append(chain);
  }
  return ciphertext;
}

bool DesCbcDecrypt(std::string_view ciphertext, std::string_view key,
                   std::string_view iv, std::string* cleartext) {
  if (key.size() != kDesKeyBytes || iv.size() != kDesBlockBytes) return false;
  if (ciphertext.empty() || ciphertext.size() % kDesBlockBytes != 0) {
    return false;
  }
  std::string chain(iv);
  std::string padded;
  padded.reserve(ciphertext.size());
  for (size_t at = 0; at < ciphertext.size(); at += kDesBlockBytes) {
    std::string_view block = ciphertext.substr(at, kDesBlockBytes);
    std::string deciphered = DesDecryptBlock(block, key);
    if (deciphered.size() != kDesBlockBytes) return false;
    padded.append(CombineBlocks(deciphered, chain));
    chain.assign(block);
  }
  auto pad = static_cast<size_t>(static_cast<uint8_t>(padded.back()));
  if (pad == 0 || pad > kDesBlockBytes || pad > padded.size()) return false;
  for (size_t n = 0; n < pad; ++n) {
    auto byte = static_cast<size_t>(
        static_cast<uint8_t>(padded[padded.size() - 1 - n]));
    if (byte != pad) return false;
  }
  padded.resize(padded.size() - pad);
  cleartext->assign(padded);
  return true;
}

}  // namespace delta
