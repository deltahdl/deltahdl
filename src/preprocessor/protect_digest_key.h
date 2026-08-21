#pragma once

#include <string>
#include <string_view>

#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"

namespace delta {

// §34.5.17 and §34.5.20 describe one arrangement between them, from its two
// ends, so what each defines is written here beside the other.
//
// A message digest is a short value standing in for a long one, and it travels
// beside the block it vouches for. Travelling in the clear it would vouch for
// nothing: whoever altered the block could recompute the digest of what they
// put in its place, and the altered block would arrive with a digest agreeing
// with it. So the digest travels encrypted, and these two keywords are where
// the sides write down what encrypted it. §34.5.17 names the cipher; §34.5.20
// carries the key. Neither opens a digest without the other -- a cipher is not
// a key, and a key says nothing about which algorithm it is a key for -- which
// is why they are spelled together rather than apart.
//
// Both take their default from the corresponding keyword of the region's data.
// A design whose digest is under the same arrangement as its data says so by
// saying nothing, so each absence is filled from the other keyword rather than
// leaving the digest with no cipher and no key named for it at all.

// The tabulated name §34.5.17.1 writes with a value against it.
inline constexpr std::string_view kDigestKeyMethodKeyword = "digest_key_method";

// The tabulated name §34.5.20.1 writes standing alone, what it carries being
// written on the line after it rather than against it. That is what spares a
// key of arbitrary encoded characters from having to be spelled as a
// pragma_value, and it makes reading the keyword a thing that spans two lines.
inline constexpr std::string_view kDigestDecryptKeyKeyword =
    "digest_decrypt_key";

// Whether `identifier` is one of the values §34.5.17 identifies an encryption
// algorithm by.
//
// The subclause tabulates no set of its own. It states that the values are the
// ones written for the keyword naming the cipher a region's data are under, so
// one table answers for both keywords and an identifier admitted for either is
// admitted for the other. A value outside that table is not thereby meaningless
// -- further identifiers are admitted and left to the implementation -- but
// what it names is not something the standard decides.
bool IsProtectDigestKeyMethodIdentifier(std::string_view identifier);

// The identifier in effect at the point the reading has reached, reported
// beside whether a default put it there rather than a directive.
//
// §34.5.17 settles the default itself, so what stands here where nothing was
// written is not this implementation's choosing: it is the cipher the region's
// data are under. What decides between the two is whether a cipher was
// specified rather than whether the keyword was mentioned, the keyword written
// with nothing against it having named a cipher no more than leaving it out
// did.
ProtectKeywordValue ProtectDigestKeyMethodInEffect(
    const ProtectKeywordScope& scope);

// The keyword written as a directive carrying `method`, for stating in the
// clear which cipher a protected region's digests are under.
//
// §34.5.17 has that identifier unchanged in the output file, the one exception
// being a digital signature, where it travels inside the key block under the
// cipher that block is encrypted with. A region without one states it here, and
// an identifier swept into an encrypted block by a region that has no such
// block would leave a reader unable to learn how a digest is opened without
// first opening the very thing that digest is there to vouch for.
//
// `method` is the pragma_value as the source wrote it, quotes and all where it
// had them, and it is written back the same way. Unchanged is meant of the
// value: an identifier written bare and returned in quotes has been changed,
// whatever it still names.
std::string ProtectDigestKeyMethodDirective(std::string_view method);

// The keyword §34.5.20.1 defines, written as a directive with `encoded_key` on
// the line after it: the key that opens a protected region's digest block.
//
// `encoded_key` is the key already written in the coding scheme the envelope
// declares, which is what §34.5.20 has that value spelled with, and it is the
// whole of that line. It is not a pragma_value and is not read as one, so a key
// is carried across whichever characters that scheme happened to spell it with.
std::string ProtectDigestDecryptKeyDirective(std::string_view encoded_key);

// The digest decryption pragma expressions a key block carries: what §34.5.20
// has an encrypting tool store there, and what it has a reader find inside.
//
// `decrypt_key` is the key itself rather than a name for one. §34.5.20 writes
// the encoded value of the key that opens a region's digest block on the line
// beneath the keyword carrying it, so what the buffer holds is the key, and a
// reader that recovered the buffer has the key in hand rather than a way of
// asking someone for it.
struct ProtectDigestDecryption {
  std::string decrypt_key;
  // The identifier naming the cipher that key is a key for. §34.5.20 has a
  // reader find it beside the key, and §34.5.17 is where the identifier is
  // defined: the two together are what opens a digest block, a key saying
  // nothing about which algorithm it belongs to.
  //
  // Empty where the region named no cipher of its own for its digests, in which
  // case §34.5.17's default is what a reader fills the place from -- the cipher
  // the region's data are under, which the envelope already states in the
  // clear.
  //
  // It is named for the keyword §34.5.17.1 spells rather than for the shorter
  // word beside it, because the field below names the keyword §34.5.21.1
  // spells and the two identifiers are not the same identifier: one says how a
  // digest is computed and the other says how the result is put under a key.
  std::string key_method;
  // The identifier naming the algorithm the region's digests were computed
  // with, which is what §34.5.21.1 spells. It travels here for the reason the
  // cipher beside it does: §34.5.21 has the identifier unchanged in the output
  // file except where a digital signature is used, and there it is encrypted
  // with the key_method and placed in a key block.
  //
  // Empty where the region stated no identifier of its own, in which case the
  // reader is left at §34.5.21's default rather than at a value the author
  // never wrote.
  std::string digest_method;
};

// Those expressions written as directives, with the key on the line beneath the
// keyword that carries it, encoded under `encoding` as §34.5.20 requires of
// that value.
//
// The key is left out where the region carries none of its own for its digests.
// §34.5.20 has this arrangement used where digital signatures are, and a region
// generating no digest signs nothing: there is no key made for a digest, so
// there is nothing for the block to carry and nothing said by writing the
// keyword with an empty line beneath it. The cipher goes in either way, that
// being where §34.5.17 has it written whenever a signature is used, and the
// algorithm the digests were computed under goes in beside it, that being where
// §34.5.21 has that identifier written whenever a signature is used.
std::string ProtectDigestDecryptionContent(
    const ProtectDigestDecryption& digest, const ProtectEncoding& encoding);

// The key §34.5.20 has an IP author generate and encrypt a region's digests
// with, derived from the key that region's data are under.
//
// It is a key of the digest's own rather than the data's. §34.5.20 gives the
// digest a key it carries separately, and the two coincide only where a text
// wrote none: a digest encrypted under the very key its data are under would be
// opened by everyone the data are opened by, which leaves the keyword carrying
// it saying nothing that could not be read without it.
//
// Deriving it from the data's key rather than drawing it at random is what lets
// one input text be encrypted twice and come out the same, which a reader
// comparing two runs of a tool depends on; the data's key is already the secret
// this arrangement keeps, so a derivation from it gives away nothing a holder
// of that key did not have.
std::string ProtectGeneratedDigestKey(std::string_view data_key);

}  // namespace delta
