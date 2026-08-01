#pragma once

#include <cstddef>
#include <string>
#include <string_view>

#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"

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

// How many bytes the block recording `cleartext` holds before that block is
// written as text. §34.5.9 has an encrypting tool state this count against the
// bytes subkeyword of the encoding it writes, so that whatever reads the block
// knows how much data the characters stand for without decoding them first.
//
// It is more than the length of the cleartext, because a block records what
// the region was as well as the region itself.
size_t ProtectedRegionBlockSize(std::string_view cleartext);

// What envelope encryption found in the text it was given that the standard
// makes an error rather than something to transform.
//
// §34.5.1 states one such condition on the expression that opens a region: a
// region opened inside a region that is still open. The point encryption
// begins at is what that expression marks, and a text marking a second such
// point without having marked where the first region ends has asked for a
// block inside a block. What the standard does allow inside an open region is
// a previously generated begin_protected-end_protected block, which is not a
// nesting of these two expressions at all: that block's own text is encrypted
// as a byte stream along with everything else the region holds, so nothing in
// it opens anything.
//
// §34.5.15 states one such condition on an encrypting tool's input: a data
// block written where no previously generated begin_protected-end_protected
// block encloses it. A block inside one of those belongs to a model that was
// protected already, and the same subclause has it passed over rather than
// objected to; a block outside every one of them belongs to no envelope at
// all, so there is nothing it can be the block of.
//
// The transformation runs to the end of the text either way, the rest of it
// being ordinary source, so what was found is reported beside the text rather
// than in place of it. A caller that does not ask for the report gets the same
// transformation and is told nothing.
// §34.5.27 states the same condition on a key block, word for word and for the
// same reason: a key block written where no previously generated block encloses
// it holds the keys of no envelope, there being nothing it could have come out
// of, while one written inside such a block belongs to a model that was
// protected already and is passed over.
//
// It also holds the key blocks of a single encryption envelope to encoding the
// same data decryption key data. Several of them are alternative ways into one
// envelope rather than ways into several, so a region whose data decryption
// pragma expressions changed value between two of them has asked for blocks
// that cannot all be the keys of the same data.
struct ProtectEncryptionReport {
  bool nested_begin_block = false;
  bool data_block_outside_protected_block = false;
  bool key_block_outside_protected_block = false;
  bool key_block_data_changed = false;
};

// Encrypts one region of cleartext under `key` and returns the text that
// records it, written in the coding scheme `enctype` names. An empty key
// encrypts nothing and returns an empty block, and so does a scheme this
// implementation does not provide.
//
// The scheme defaults to this implementation's own, which is what a region
// encrypted by a text that stated no encoding is written in. Its alphabet
// holds letters, digits and two punctuation characters only, so a block of it
// can be written as the value of a pragma expression without any of it being
// read as something else.
std::string EncryptProtectedRegion(std::string_view cleartext,
                                   std::string_view key,
                                   std::string_view enctype = kBlockEnctype);

// The inverse, taking the block as the bytes it holds rather than as the text
// it was written as: recovers into `*cleartext` the region those bytes record.
//
// Reading a block out of the coding scheme it was written in is a separate
// step, and §34.5.9 makes it one that every encoded value of an envelope goes
// through alike, so it is left to the caller rather than done again here. What
// remains is the part that is about the key: this returns false, leaving
// `*cleartext` untouched, when `key` is not the key the region was encrypted
// under -- an empty key, a different key, and bytes this encryption never
// produced all reach here the same way.
bool DecryptProtectedBlock(std::string_view block, std::string_view key,
                           std::string* cleartext);

// The two steps together, for a caller holding a block as the text it was
// written as: reads `data_block` out of the scheme `enctype` names and then
// recovers the region the bytes record. False where either step fails.
bool DecryptProtectedRegion(std::string_view data_block, std::string_view key,
                            std::string* cleartext,
                            std::string_view enctype = kBlockEnctype);

// Envelope encryption over a whole source text. Every encryption envelope in
// `source_text` comes back a decryption envelope carrying its body encrypted
// under a key and recorded on a data_block expression, and every character
// outside those envelopes comes back exactly as it was written.
//
// Which key a region is encrypted under is settled by §34.5.10: the entity a
// region names as having provided the keys is what selects the key that
// encrypts that region's block, so a text naming several entities has each of
// its regions encrypted under a key of the entity that region names. `keys`
// holds the keys supplied under the names that select them, and `exchange_key`
// is what a user holding a single key supplies instead -- one key for every
// region, whoever the region names. A region left with no key is a region with
// nothing to encrypt it under, so it is returned as it was written, and a text
// with neither kind of key supplied is returned whole.
//
// An envelope is transformed rather than replaced: the expressions the source
// wrote beside each delimiter specified that envelope, so they are carried on
// to the envelope taking its place, and only the two words naming the
// delimiters change. Expressions the enclosed text held describe that text and
// are encrypted along with it, except for the two the standard has written in
// the clear: which key the data are under, and whose.
//
// A previously generated begin_protected-end_protected block standing in the
// input is not read as description at all. §34.5.3 has the contents of such a
// block treated as input cleartext, so its protect pragma expressions are not
// interpreted and none of them overrides what the reading has in effect: an
// already-protected model can be sealed inside a larger one without its own
// description of itself displacing the larger one's. Those lines are carried
// as the bytes they are written with, into the block of whichever encryption
// envelope encloses them, which is what §34.5.3 and §34.5.4 have become of
// the two expressions delimiting them.
//
// A region that names no key of its own is encrypted under the key its names
// select directly. §34.5.27 settles the other arrangement: a region designating
// a key of the entity that provided the keys its own keys are under has asked
// for a digital signature, so the tool makes a key for that region, encrypts
// the region under it, and writes that key into the envelope inside a key block
// encrypted under the designated key. One block is written per designation the
// region carries, those being alternative ways into the one envelope.
//
// `report` collects what §34.5.1, §34.5.15 and §34.5.27 make an error in the
// input, and may be null for a caller with nothing to report it to.
//
// All three are conditions on the text rather than on the keys, so a caller
// asking for one gets the text read through even where no key was supplied and
// no region could be encrypted. The text handed back in that case is the text
// that went in, there being nothing to transform it into.
std::string EncryptEnvelopes(std::string_view source_text,
                             std::string_view exchange_key,
                             const ProtectKeyList& keys = ProtectKeyList(),
                             ProtectEncryptionReport* report = nullptr);

}  // namespace delta
