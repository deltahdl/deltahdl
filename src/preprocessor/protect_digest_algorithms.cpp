#include "preprocessor/protect_digest_algorithms.h"

#include <array>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <span>
#include <string>
#include <string_view>

namespace delta {
namespace {

constexpr size_t kBlockBytes = 64;

constexpr size_t kLengthOffset = 56;

constexpr size_t kLengthBytes = 8;
constexpr size_t kWordBytes = 4;

enum class DigestByteOrder : uint8_t {
  kLeastSignificantFirst,
  kMostSignificantFirst
};

size_t ByteShift(size_t index, size_t width, DigestByteOrder order) {
  if (order == DigestByteOrder::kLeastSignificantFirst) return index * 8;
  return (width - 1 - index) * 8;
}

uint32_t RotateLeft(uint32_t word, size_t bits) {
  return (word << bits) | (word >> (32 - bits));
}

std::string PaddedMessage(std::string_view bytes, DigestByteOrder order) {
  std::string message(bytes);
  message.push_back(static_cast<char>(0x80));
  while (message.size() % kBlockBytes != kLengthOffset) {
    message.push_back('\0');
  }
  uint64_t bits = static_cast<uint64_t>(bytes.size()) * 8;
  for (size_t i = 0; i < kLengthBytes; ++i) {
    size_t shift = ByteShift(i, kLengthBytes, order);
    message.push_back(static_cast<char>((bits >> shift) & 0xff));
  }
  return message;
}

uint32_t WordAt(std::string_view block, size_t offset, DigestByteOrder order) {
  uint32_t word = 0;
  for (size_t i = 0; i < kWordBytes; ++i) {
    auto byte =
        static_cast<uint32_t>(static_cast<unsigned char>(block[offset + i]));
    word |= byte << ByteShift(i, kWordBytes, order);
  }
  return word;
}

std::string DigestOf(std::span<const uint32_t> state, DigestByteOrder order) {
  std::string digest;
  for (uint32_t word : state) {
    for (size_t i = 0; i < kWordBytes; ++i) {
      size_t shift = ByteShift(i, kWordBytes, order);
      digest.push_back(static_cast<char>((word >> shift) & 0xff));
    }
  }
  return digest;
}

constexpr size_t kMd5Rounds = 64;

constexpr std::array<uint32_t, 4> kMd5InitialState = {
    0x67452301,
    0xefcdab89,
    0x98badcfe,
    0x10325476,
};

constexpr std::array<std::array<size_t, 4>, 4> kMd5Rotations = {
    std::array<size_t, 4>{7, 12, 17, 22},
    std::array<size_t, 4>{5, 9, 14, 20},
    std::array<size_t, 4>{4, 11, 16, 23},
    std::array<size_t, 4>{6, 10, 15, 21},
};

size_t Md5RotationOf(size_t round) {
  return kMd5Rotations[round / 16][round % 4];
}

std::array<uint32_t, kMd5Rounds> Md5SineConstants() {
  std::array<uint32_t, kMd5Rounds> constants{};
  for (size_t round = 0; round < kMd5Rounds; ++round) {
    double magnitude = std::fabs(std::sin(static_cast<double>(round + 1)));
    constants[round] =
        static_cast<uint32_t>(std::floor(magnitude * 4294967296.0));
  }
  return constants;
}

const std::array<uint32_t, kMd5Rounds>& Md5Constants() {
  static const std::array<uint32_t, kMd5Rounds> kConstants = Md5SineConstants();
  return kConstants;
}

struct Md5Step {
  uint32_t mixed;
  size_t word;
};

Md5Step Md5StepOf(size_t round, uint32_t b, uint32_t c, uint32_t d) {
  if (round < 16) return {(b & c) | (~b & d), round};
  if (round < 32) return {(d & b) | (~d & c), ((5 * round) + 1) % 16};
  if (round < 48) return {b ^ c ^ d, ((3 * round) + 5) % 16};
  return {c ^ (b | ~d), (7 * round) % 16};
}

void Md5Block(std::string_view block, std::array<uint32_t, 4>* state) {
  constexpr DigestByteOrder kOrder = DigestByteOrder::kLeastSignificantFirst;
  std::array<uint32_t, 4> working = *state;
  for (size_t round = 0; round < kMd5Rounds; ++round) {
    Md5Step step = Md5StepOf(round, working[1], working[2], working[3]);
    uint32_t word = WordAt(block, step.word * kWordBytes, kOrder);
    uint32_t sum = working[0] + step.mixed + Md5Constants()[round] + word;
    working[0] = working[3];
    working[3] = working[2];
    working[2] = working[1];
    working[1] += RotateLeft(sum, Md5RotationOf(round));
  }
  for (size_t i = 0; i < working.size(); ++i) (*state)[i] += working[i];
}

constexpr size_t kSha1Rounds = 80;

constexpr size_t kSha1BlockWords = 16;

constexpr std::array<uint32_t, 5> kSha1InitialState = {
    0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0,
};

struct Sha1Step {
  uint32_t mixed;
  uint32_t constant;
};

Sha1Step Sha1StepOf(size_t round, uint32_t b, uint32_t c, uint32_t d) {
  if (round < 20) return {(b & c) | (~b & d), 0x5a827999};
  if (round < 40) return {b ^ c ^ d, 0x6ed9eba1};
  if (round < 60) return {(b & c) | (b & d) | (c & d), 0x8f1bbcdc};
  return {b ^ c ^ d, 0xca62c1d6};
}

std::array<uint32_t, kSha1Rounds> Sha1Schedule(std::string_view block) {
  constexpr DigestByteOrder kOrder = DigestByteOrder::kMostSignificantFirst;
  std::array<uint32_t, kSha1Rounds> schedule{};
  for (size_t i = 0; i < kSha1BlockWords; ++i) {
    schedule[i] = WordAt(block, i * kWordBytes, kOrder);
  }
  for (size_t i = kSha1BlockWords; i < kSha1Rounds; ++i) {
    uint32_t mixed =
        schedule[i - 3] ^ schedule[i - 8] ^ schedule[i - 14] ^ schedule[i - 16];
    schedule[i] = RotateLeft(mixed, 1);
  }
  return schedule;
}

void Sha1Block(std::string_view block, std::array<uint32_t, 5>* state) {
  std::array<uint32_t, kSha1Rounds> schedule = Sha1Schedule(block);
  std::array<uint32_t, 5> working = *state;
  for (size_t round = 0; round < kSha1Rounds; ++round) {
    Sha1Step step = Sha1StepOf(round, working[1], working[2], working[3]);
    uint32_t sum = RotateLeft(working[0], 5) + step.mixed + working[4] +
                   step.constant + schedule[round];
    working[4] = working[3];
    working[3] = working[2];
    working[2] = RotateLeft(working[1], 30);
    working[1] = working[0];
    working[0] = sum;
  }
  for (size_t i = 0; i < working.size(); ++i) (*state)[i] += working[i];
}

}  // namespace

std::string Md5Digest(std::string_view bytes) {
  constexpr DigestByteOrder kOrder = DigestByteOrder::kLeastSignificantFirst;
  std::array<uint32_t, 4> state = kMd5InitialState;
  std::string message = PaddedMessage(bytes, kOrder);
  for (size_t at = 0; at < message.size(); at += kBlockBytes) {
    Md5Block(std::string_view(message).substr(at, kBlockBytes), &state);
  }
  return DigestOf(state, kOrder);
}

std::string Sha1Digest(std::string_view bytes) {
  constexpr DigestByteOrder kOrder = DigestByteOrder::kMostSignificantFirst;
  std::array<uint32_t, 5> state = kSha1InitialState;
  std::string message = PaddedMessage(bytes, kOrder);
  for (size_t at = 0; at < message.size(); at += kBlockBytes) {
    Sha1Block(std::string_view(message).substr(at, kBlockBytes), &state);
  }
  return DigestOf(state, kOrder);
}

}  // namespace delta
