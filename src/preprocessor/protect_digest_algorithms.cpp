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

// Both algorithms read a message a block at a time, and a block is the same
// size in each.
constexpr size_t kBlockBytes = 64;

// Where within the final block the message length is written: it occupies the
// last eight bytes, so the padding runs up to this point and the length fills
// the rest.
constexpr size_t kLengthOffset = 56;

// How many bytes the message length occupies, and how many a word does.
constexpr size_t kLengthBytes = 8;
constexpr size_t kWordBytes = 4;

// Which end of a multi-byte number is written first. The two algorithms agree
// on everything about their padding except this: MD5 writes the message length
// and reads each word of a block from its least significant byte, and SHA-1
// does both from the most significant one.
enum class DigestByteOrder : uint8_t {
  kLeastSignificantFirst,
  kMostSignificantFirst
};

// How far a number `width` bytes wide has to be shifted for the byte written at
// position `index` to be the low one, counting positions from the front of the
// writing.
size_t ByteShift(size_t index, size_t width, DigestByteOrder order) {
  if (order == DigestByteOrder::kLeastSignificantFirst) return index * 8;
  return (width - 1 - index) * 8;
}

// A thirty-two bit word rotated left by `bits`, the operation both algorithms
// are built out of. Every rotation either of them asks for is by between one
// and thirty-one places, so each half of the result is a shift the word has
// room for.
uint32_t RotateLeft(uint32_t word, size_t bits) {
  return (word << bits) | (word >> (32 - bits));
}

// The message with the padding both algorithms end it with: one byte carrying
// only its top bit, then zero bytes up to the point the length is written at,
// then the length of the original message counted in bits.
//
// The marker byte is padding rather than something the message may be short of,
// so a message that already reaches the point the length is written at is
// carried into a further block instead of having its own last bytes written
// over.
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

// One word of a block, read from the four bytes at `offset` in the order the
// algorithm reading it writes its words in.
uint32_t WordAt(std::string_view block, size_t offset, DigestByteOrder order) {
  uint32_t word = 0;
  for (size_t i = 0; i < kWordBytes; ++i) {
    auto byte =
        static_cast<uint32_t>(static_cast<unsigned char>(block[offset + i]));
    word |= byte << ByteShift(i, kWordBytes, order);
  }
  return word;
}

// The state words written out as the digest, each word's bytes in the order
// that algorithm writes them. The digest is those words and nothing else, so
// how long it is follows from how many of them the algorithm carries.
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

// How many rounds MD5 puts each block through.
constexpr size_t kMd5Rounds = 64;

// The four words RFC 1321 starts the state at.
constexpr std::array<uint32_t, 4> kMd5InitialState = {
    0x67452301,
    0xefcdab89,
    0x98badcfe,
    0x10325476,
};

// How far the accumulated word is turned in each round. RFC 1321 uses four
// rotations to a group and four groups to the sixty-four rounds, and inside a
// group each rotation is used on four rounds running, so the group is chosen by
// which quarter of the rounds this one falls in and the rotation by where the
// round stands within its four.
constexpr std::array<std::array<size_t, 4>, 4> kMd5Rotations = {
    std::array<size_t, 4>{7, 12, 17, 22},
    std::array<size_t, 4>{5, 9, 14, 20},
    std::array<size_t, 4>{4, 11, 16, 23},
    std::array<size_t, 4>{6, 10, 15, 21},
};

size_t Md5RotationOf(size_t round) {
  return kMd5Rotations[round / 16][round % 4];
}

// The constant added in each round. RFC 1321 defines the one belonging to round
// i as the whole part of the sine of i radians, taken without its sign and
// scaled by two to the thirty-second, and prints the sixty-four values that
// works out to. They are computed from the definition here rather than copied
// from that printing, the definition being the shorter of the two to check and
// a table of that size being checked against the definition anyway.
//
// The scaled magnitude stays below two to the thirty-second, the sine of a
// whole number of radians never reaching one, so every value it takes is one a
// thirty-two bit word holds.
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

// What one round of MD5 contributes: the value three of the state words are
// mixed into, and which word of the block the round reads. RFC 1321 changes
// both every sixteen rounds, so the round number decides them together.
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

// One block folded into the state: the four words are worked on for sixty-four
// rounds, and what the rounds left is added to the state the block started
// from, so a block moves the state rather than replacing it.
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

// How many rounds SHA-1 puts each block through, which is also how many words
// the block is expanded into to feed them.
constexpr size_t kSha1Rounds = 80;

// How many of those words are read from the block itself; the rest are worked
// out from the ones before them.
constexpr size_t kSha1BlockWords = 16;

// The five words FIPS 180-2 starts the state at. It carries one word more than
// the other algorithm, which is why its digest is four bytes longer.
constexpr std::array<uint32_t, 5> kSha1InitialState = {
    0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0,
};

// What one round of SHA-1 contributes: the value three of the state words are
// mixed into, and the constant added beside it. FIPS 180-2 changes both every
// twenty rounds.
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

// The eighty words one block feeds the rounds: the sixteen the block is written
// with, and then each further word from four of the words already worked out,
// combined and turned by one place.
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

// One block folded into the state, on the same terms as the other algorithm:
// the five words are worked on for eighty rounds and what the rounds left is
// added to the state the block started from.
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

// The message is read a block at a time from the front. The padding is what
// makes the number of blocks whole, so the walk needs no special last step.
std::string Md5Digest(std::string_view bytes) {
  constexpr DigestByteOrder kOrder = DigestByteOrder::kLeastSignificantFirst;
  std::array<uint32_t, 4> state = kMd5InitialState;
  std::string message = PaddedMessage(bytes, kOrder);
  for (size_t at = 0; at < message.size(); at += kBlockBytes) {
    Md5Block(std::string_view(message).substr(at, kBlockBytes), &state);
  }
  return DigestOf(state, kOrder);
}

// The same walk over the same block size, differing in the state it starts
// from, the end each number is written from, and the rounds a block is put
// through.
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
