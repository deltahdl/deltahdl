#pragma once

#include <cstdint>
#include <string>
#include <string_view>

#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"

namespace delta {

// §34.5.22 settles what a protected envelope carries so that a reader can tell
// the design an author sealed from a design somebody else put in its place.
//
// A message digest is a fixed-size value computed from a set of data, and no
// other set of data is expected to reach the same one. Written beside the block
// it was computed from, it lets whatever reads the block compute the digest
// again and compare: two digests that agree say the block arrived as it was
// sealed, and two that disagree say either the block or the digest beside it
// was altered on the way. This subclause defines the expression a digest
// travels on, what an encrypting tool has to have settled before it can write
// one, and what a consuming tool does with one it finds.
//
// A digest is owed to each block an encryption produces -- the block holding
// the design and every block holding the keys -- and it follows immediately the
// block it refers to, so that a reader never has to decide which of several
// blocks a digest belongs to.

// The tabulated name §34.5.22.1 writes standing alone, the digest it carries
// being written on the line after it rather than against it. That is what
// spares a block of arbitrary encoded characters from having to be spelled as a
// pragma_value, and it makes reading the keyword a thing that spans two lines.
inline constexpr std::string_view kDigestBlockKeyword = "digest_block";

// What §34.5.22 has an encrypting tool settle before it can write a digest at
// all: whether one was asked for, how it is computed, and what it is encrypted
// under.
//
// The three travel together because none of them produces a digest on its own.
// A digest nobody asked for is not written; a digest computed under an
// algorithm nothing here provides is not a digest; and a digest written in the
// clear vouches for nothing, since whoever altered the block could compute the
// digest of what they put in its place.
struct ProtectDigestBlockPolicy {
  // Whether the input asked for a digest. §34.5.22 makes a digest_block written
  // in an input file outside every previously generated protected block a
  // request to generate one in the output file, so a text that wrote none has
  // asked for none and its envelopes carry no digest.
  bool requested = false;
  // The identifier naming the algorithm the digest is computed with, which is
  // what the keyword naming the digest algorithm specifies. A text that named
  // none leaves §34.5.21's default standing here, so there is always an
  // algorithm to compute under.
  std::string method;
  // That same identifier as the text stated it, quotation marks and all where
  // it had them, and empty where the text stated none.
  //
  // It is kept beside the resolved one because the two answer different
  // questions. §34.5.21 has the identifier unchanged wherever it is written
  // out, and a text that stated none has nothing to write out, so a default
  // standing in the field above must not become an identifier the envelope
  // claims its author chose. What reads this is the key block: §34.5.21 puts
  // the identifier inside one wherever a digital signature is used, and a
  // value written bare that came back in quotes is a different pragma_value
  // from the one the author wrote.
  std::string stated_method;
  // The identifier naming the cipher the digest is encrypted under. §34.5.22
  // sends the reader to the keyword naming that cipher and, in its absence, to
  // the cipher the region's data are under. It is recorded so that it can be
  // written beside the key for whatever reads the digest; this implementation
  // offers one cipher, so nothing here selects among ciphers with it.
  std::string key_method;
  // The name the region gave the key its digest is encrypted with, as the text
  // spelled it and empty where the text spelled none.
  //
  // §34.5.22 picks that key out by the designations the region wrote for it,
  // and §34.5.18 defines this one. It is recorded because §34.5.18.2 has the
  // name encoded in the key block wherever a digital envelope mechanism is
  // used, rather than written in the clear, and a name nothing kept cannot be
  // written there.
  std::string keyname;
  // The key the digest is encrypted with, which §34.5.22 has picked out by the
  // designations the region wrote for its digest's key.
  std::string key;
};

// One digest block, written whole: the encoding expression stating how much
// data the block stands for, the keyword announcing it, and, on the line after
// that keyword, the digest of `cleartext` encrypted under the policy's key and
// written in the scheme `encoding` names.
//
// §34.5.22 encodes the digest under the encoding pragma expression in effect
// and output on the line following the keyword announcing it, which is where a
// reader of that keyword goes looking for it.
//
// The result is empty where there is no digest to write: where the input asked
// for none, where the algorithm named is one this implementation does not
// provide, and where no key was reached to encrypt one under. A digest that
// could not be produced is left out rather than written short or written under
// whichever algorithm was nearest to hand, since a reader recomputing it would
// find a value disagreeing with a block that arrived exactly as it was sealed.
std::string ProtectDigestBlockDirectives(std::string_view cleartext,
                                         const ProtectDigestBlockPolicy& policy,
                                         const ProtectEncoding& encoding);

// What §34.5.22 has a consuming tool hold ready by the time it reaches a digest
// block: the cleartext of the block that digest refers to, and the key the
// digest is under.
//
// The cleartext is what the reading recovered rather than the characters the
// block was written as, because that is what the digest was computed from: the
// tool that wrote it generated the digest from the data, and the tool that
// reads it generates a digest from the data it decrypted.
struct ProtectDigestTarget {
  std::string cleartext;
  std::string key;
};

// How comparing the digest a block carries against the block it refers to came
// out.
//
// A block that does not open and a block whose digest could not be recomputed
// are held apart from a block whose two digests disagree. Only the last of them
// says something happened to the data: the first two say the reading was never
// in a position to check, which a reader holding one entity's key rather than
// another's is in for every digest not written for it.
//
// A reading that has reached no digest block at all is a fourth thing again. A
// text carrying no digest was never asked to carry one, so nothing about it
// went unchecked; saying that with the value that means a check failed would
// put every unsigned text in the same state as a tampered one.
enum class ProtectDigestCheck : uint8_t {
  kNotChecked,
  kMatched,
  kAltered,
  kUnreadable,
};

// Which of the three the digest in `block` is in. `block` is the bytes the
// digest block records, the characters it was written as having already been
// read out of the coding scheme in effect where it stood, and `method` names
// the algorithm the digest is regenerated under.
//
// §34.5.22 has a consuming tool decrypt the encrypted data, generate a digest
// from what it decrypted, decrypt the digest the block carries, and compare the
// two. Two that disagree say either the block carrying the digest or the
// encrypted data was altered since the input data was encrypted; which of the
// two it was is not something the comparison can tell, so neither is named.
ProtectDigestCheck CheckProtectDigestBlock(std::string_view block,
                                           const ProtectDigestTarget& target,
                                           std::string_view method);

// The key that the entity a region named for its digest and the public key one
// of that entity's keys is select together out of `keys`.
//
// §34.5.22 lists four designations a digest's key is picked out by, and this is
// the one that is neither the name given to a key nor a key carried inside the
// envelope. Neither half reaches a key on its own -- a designation is a
// member of one entity's list and means nothing outside it -- so the two are
// combined rather than tried apart.
//
// It is an alternative to the name given to the key rather than a companion of
// it, which is why a caller tries it where that name reaches nothing rather
// than instead of that name: a region writing both has picked out one key
// twice, so which is consulted first decides nothing, while a region writing
// only this one would be left designating nothing at all if the name were the
// only route.
//
// The result is empty where the region designated no public key for its digest,
// and where the pair reaches none of the keys held.
std::string_view ProtectDigestKeyByPublicKey(const ProtectKeywordScope& scope,
                                             const ProtectKeyList& keys);

}  // namespace delta
