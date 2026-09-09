#pragma once

#include <cstddef>
#include <string>
#include <string_view>

namespace delta {

// FIPS 46-3's Data Encryption Standard, and the CBC mode §34.5.11.2's Table
// 34-3 names `des-cbc` and marks required of every implementation.
//
// The cipher is written here rather than reached through a library because
// nothing this tree builds links one, and it is written from the published
// algorithm: the permutations, the key schedule and the eight substitution
// boxes are the standard's own tables. A cipher is a function whose answer is
// stated for given inputs, so what says this is DES rather than something
// self-consistent is the known-answer cases in
// test/src/unit/test_preprocessor_subclause_34_05_11_02.cpp, which take the
// published vectors: a round trip alone closes over any invertible function.

// The width of one block and one key, which FIPS 46-3 fixes at 64 bits each.
// The key's low bit of every byte is a parity bit the algorithm never reads, so
// a key is 64 bits written and 56 bits used.
inline constexpr size_t kDesBlockBytes = 8;
inline constexpr size_t kDesKeyBytes = 8;

// One block enciphered under one key, each written as kDesBlockBytes bytes with
// the most significant first -- the order FIPS 46-3 numbers the bits of a block
// in, bit 1 being the leftmost. A block or a key of any other length is not one
// the algorithm is defined over and yields the empty string.
std::string DesEncryptBlock(std::string_view block, std::string_view key);

// The inverse, which is the same computation with the sixteen subkeys applied
// in the reverse order.
std::string DesDecryptBlock(std::string_view block, std::string_view key);

// §34.5.11.2's des-cbc over `cleartext`: each block is combined with the
// preceding cipher-block before it is enciphered, `iv` standing in for the
// block before the first. §34.5.15.2 has that IV travel ahead of the encrypted
// data rather than inside it, so it is a parameter here rather than a prefix of
// what comes back.
//
// The cleartext is padded to a whole number of blocks the way IETF RFC 5652
// pads, every byte of the padding holding the number of padding bytes, and a
// cleartext already a whole number of blocks long is given a whole block of
// padding so that the reading can always take a padding count off the end.
// §34.5 names no padding of its own and a block cipher cannot do without one.
std::string DesCbcEncrypt(std::string_view cleartext, std::string_view key,
                          std::string_view iv);

// The inverse. False where the ciphertext is not a whole number of blocks or
// where the padding it recovers to is not padding this would have written,
// which is what a block deciphered under the wrong key almost always leaves.
bool DesCbcDecrypt(std::string_view ciphertext, std::string_view key,
                   std::string_view iv, std::string* cleartext);

}  // namespace delta
