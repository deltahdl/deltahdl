#pragma once

#include <string>
#include <string_view>

namespace delta {

// The message digest algorithms Table 34-4 names, each written as the
// transformation it is: a run of bytes of any length in, a fixed number of
// bytes out. The same run always gives the same value, and a run altered
// anywhere gives a different one, which is what lets a digest stand for a block
// far larger than itself.
//
// Every byte of the run is data. A digest is computed over what a block holds
// rather than over what is printable in it, so a run holding a zero byte
// continues past it and a run holding bytes with the high bit set is no
// different from any other.
//
// What each of these produces is the digest itself, as the bytes the published
// algorithm defines. Writing those bytes as characters is a separate step and
// another subclause's: §34.5.9 settles the coding scheme every encoded value
// of a protected envelope is written under, and a digest is one of them.

// SHA-1, as FIPS 180-2 defines it: twenty bytes.
std::string Sha1Digest(std::string_view bytes);

// MD5, as IETF RFC 1321 defines it: sixteen bytes.
//
// The two agree on the shape of the computation -- the message padded out to a
// whole number of sixty-four byte blocks and each block folded into a running
// state -- and differ in the end a multi-byte number is written from, in how
// many words of state they carry, and in the rounds each block is put through.
std::string Md5Digest(std::string_view bytes);

}  // namespace delta
