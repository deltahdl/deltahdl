#pragma once

#include <string>
#include <string_view>

namespace delta {

// §34.3 gives a protected envelope two modes of processing, and each is a
// transformation of one text into another.
//
// Envelope encryption reads the encryption envelopes written in a source text
// and leaves a decryption envelope in the place of each one. Envelope
// decryption reads the decryption envelopes of an input text and puts back the
// cleartext each of them stands for, so that the compilation step after it
// analyses the design the envelope was formed from rather than the envelope.
//
// The two are inverses under one key: encrypting a region and decrypting the
// result with the same key gives the region back character for character. The
// standard leaves the algorithm to the implementation; what it fixes is that
// the pair round-trips and that the key is what decides whether the second
// half of the pair can run at all.
//
// The rule that shapes the encrypting half is that only protect pragma
// directives are processed. Every other character of the text -- a macro
// definition, an include, a directive belonging to some other pragma, or text
// that is not SystemVerilog at all -- is carried across as the bytes it is
// written with, so nothing about it is interpreted on the way.
//
// The key an IP author gives an encrypting tool, and that a tool decrypting
// what it produced is given in turn, is the exchange key. One key doing both
// makes this a symmetric algorithm and its key a symmetric key: there is no
// second key that decrypts what the first one encrypted, and none is needed.
//
// The other arrangement the standard describes is a session key -- a key made
// for one region, recorded in the envelope encrypted under the exchange key,
// with the region encrypted under it. A tool may offer that and this one does
// not, so a region here is encrypted under the exchange key directly and the
// envelope records no key beside it.

// The pragma expression that carries an encrypted region across a decryption
// envelope. The region's own text is not written in the envelope, so the
// expression's value is where envelope decryption looks for it.
inline constexpr std::string_view kDataBlockKeyword = "data_block";

// Encrypts one region of cleartext under `key` and returns the text that
// records it. The result is spelled with letters, digits and two punctuation
// characters only, so it can be written as the value of a pragma expression
// without any of it being read as something else. An empty key encrypts
// nothing and returns an empty block.
std::string EncryptProtectedRegion(std::string_view cleartext,
                                   std::string_view key);

// The inverse: recovers into `*cleartext` the region that `data_block`
// records. Returns false, leaving `*cleartext` untouched, when `key` is not
// the key the region was encrypted under -- an empty key, a different key, or
// a block that this encryption never produced all reach here the same way.
bool DecryptProtectedRegion(std::string_view data_block, std::string_view key,
                            std::string* cleartext);

// Envelope encryption over a whole source text. Every encryption envelope in
// `source_text` comes back a decryption envelope carrying its body encrypted
// under `exchange_key` and recorded on a data_block expression, and every
// character outside those envelopes comes back exactly as it was written. With
// an empty key there is nothing to encrypt under, so the text is returned as
// it stands.
//
// An envelope is transformed rather than replaced: the expressions the source
// wrote beside each delimiter specified that envelope, so they are carried on
// to the envelope taking its place, and only the two words naming the
// delimiters change. Expressions the enclosed text held describe that text and
// are encrypted along with it.
std::string EncryptEnvelopes(std::string_view source_text,
                             std::string_view exchange_key);

}  // namespace delta
