#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"

namespace delta {

// §34.5.27 and §34.5.14 describe one arrangement between them, from its two
// ends, so what each defines is written here beside the other.
//
// A region encrypted under a key its reader already holds carries no key at
// all. The other arrangement is this one: the tool makes a key for the region,
// encrypts the region under that key, and sends the key along inside the
// envelope, itself encrypted under a key of the entity the region named for its
// own keys. §34.5.27 defines the block that key travels in; §34.5.14 defines
// the keyword that carries the key inside that block. Neither reaches a key
// without the other -- the block is where the keyword is written, and the
// keyword is what the block is opened for -- which is why they are spelled
// together rather than apart.
//
// Both keywords are written standing alone, with what they announce on the line
// after them. That is what spares a block of arbitrary encoded characters from
// having to be spelled as a pragma_value, and it makes reading either of them a
// thing that spans two lines.

// The tabulated name of the keyword that announces a key block. §34.5.27.1
// writes it standing alone.
inline constexpr std::string_view kKeyBlockKeyword = "key_block";

// The keyword §34.5.14.1 defines, written as a directive with `encoded_key` on
// the line after it: the key that opens a protected region's data block.
//
// `encoded_key` is the key already written in the coding scheme the envelope
// declares, which is what §34.5.14 has that value spelled with, and it is the
// whole of that line. It is not a pragma_value and is not read as one, so a key
// is carried across whichever characters that scheme happened to spell it with.
std::string ProtectDataDecryptKeyDirective(std::string_view encoded_key);

// The data decryption pragma expressions a key block carries: what §34.5.27
// forms its buffer from, and what §34.5.14 has a reader find inside it.
//
// `decrypt_key` is the key itself rather than a name for one. §34.5.14 writes
// the encoded value of the key that opens a region's data block on the line
// beneath the keyword carrying it, so what the buffer holds is the key, and a
// reader that recovered the buffer has the key in hand rather than a way of
// asking someone for it.
struct ProtectDataDecryption {
  std::string decrypt_key;
  // The identifier naming the cipher the region's data are under. §34.5.14 has
  // a reader find it beside the key, the two together being what opens the data
  // block: a key says nothing about which algorithm it is a key for.
  std::string method;
  // The name §34.5.12 gives the key the data are under, empty where the region
  // gave none.
  //
  // It is recorded rather than written into the buffer. §34.5.12 already has it
  // in the clear in the envelope, so a copy inside the block would be read a
  // second time by the same reading and say nothing the first did not. What it
  // is here for is the requirement §34.5.27 makes of a region asking for
  // several blocks: it is one of the data decryption pragma expressions those
  // blocks are held to agreeing on, and an agreement cannot be checked against
  // a value nothing kept.
  std::string keyname;
};

// Whether two requests recorded the same data decryption pragma expressions.
//
// The key is not among them. One key serves every block of a region, being made
// once for the region rather than once per block, so it is the same in every
// request by construction and could never be what two of them differ over.
bool SameProtectDataDecryption(const ProtectDataDecryption& a,
                               const ProtectDataDecryption& b);

// One key block an encryption envelope asks for: the designation of the key
// that block is encrypted under, and the data decryption pragma expressions
// standing where the region asked for it.
//
// The designation is whichever of the two §34.5.23 admits was written -- the
// name given to one of the entity's keys, or the public key one of them is --
// because §34.5.26 makes the two alternatives rather than halves of one thing.
// Neither reaches a key without the entity beside it, a key name being a member
// of one entity's list and naming nothing outside it, so the entity travels on
// the request with the designation rather than apart from it.
struct ProtectKeyBlockRequest {
  std::string keyowner;
  // The entity as the source spelled it, quotation marks and all where it had
  // them, beside the body of that value the field above holds.
  //
  // The two are kept apart because they answer different questions. Reaching a
  // key is a question about what the value denotes, and §34.5.12 identifies a
  // key by the characters inside the quotation marks; writing the entity into
  // the block's own directive is a question about what the value is, and
  // §34.5.23 has it unchanged wherever the tool writes it out. §22.5.1 gives a
  // pragma_value more than one spelling, so a name written bare and returned in
  // quotes is a different pragma_value from the one the author wrote.
  std::string stated_keyowner;
  std::string keyname;
  std::string public_key;
  ProtectDataDecryption data;
  // The 1-based line of the input the designation was written on. §34.5.27
  // holds the blocks of one envelope to encoding the same data decryption key
  // data, and what tells somebody which two blocks disagreed is where each was
  // asked for, so the position travels on the request rather than being
  // recovered afterwards from a text the request no longer names.
  uint32_t line = 0;
};

// The key blocks one encryption envelope asks for, in the order it asked.
//
// §34.5.27 has several of them stand for alternative ways into a single
// decryption envelope rather than for several envelopes, so a designation
// written a second time asks for a further block beside the first rather than
// replacing it: two entities named inside one region are two readers, each
// holding a key of their own, and each is owed a block.
class ProtectKeyBlockRequests {
 public:
  // Records that the region designated one of `keyowner`'s keys by the name
  // given to it, with `data` the data decryption pragma expressions in effect
  // where the designation was written and `line` the 1-based line of the input
  // it was written on.
  void Designate(std::string_view keyowner, std::string_view keyname,
                 const ProtectDataDecryption& data, uint32_t line);

  // The same, for the designation §34.5.26 writes as a public key. `key` is the
  // key itself, the line that carried it having already been read out of the
  // scheme it was encoded under.
  void DesignatePublicKey(std::string_view keyowner, std::string_view key,
                          const ProtectDataDecryption& data, uint32_t line);

  const std::vector<ProtectKeyBlockRequest>& Requests() const {
    return requests_;
  }
  bool Empty() const { return requests_.empty(); }

 private:
  std::vector<ProtectKeyBlockRequest> requests_;
};

// What §34.5.27 has an encrypting tool produce for one region.
//
// The blocks are alternative ways into one envelope, so they all carry the one
// key the region's data are under. A region no request reached a key for is a
// region no digital signature could be produced for: there is nothing to
// encrypt a block under, so there is no key made for the data either, and both
// halves come back empty together rather than leaving a region encrypted under
// a key nothing carries.
struct ProtectKeyBlocks {
  std::string data_key;
  // The key §34.5.20 has the region's digests encrypted under, made for the
  // region alongside the key its data are under and carried in the same blocks.
  // A region whose data need no block of their own has no digest key of its own
  // either: its digest is under the key its data are under, which is where
  // §34.5.20's default sends a text that named none.
  std::string digest_key;
  std::string directives;
  // The 1-based line of the input the first request that disagreed with the
  // first one was written on, and zero where they all agreed. §34.5.27 has
  // every key block of one envelope encode the same data decryption key data,
  // so a region that changed them between two of them asked for blocks that
  // cannot all be the keys of the same data.
  //
  // It is the line rather than a bare yes because that is what somebody told
  // about the disagreement has to be given: a region designating several
  // readers writes its blocks over as many lines, and a report standing at none
  // of them leaves an author to find which two blocks differ by rereading the
  // whole region.
  uint32_t data_changed_line = 0;
};

// The key a tool makes for one region: the key §34.5.14 has an IP author
// generate and encrypt the cleartext with.
//
// It is derived from the region and from the key the block carrying it will be
// encrypted under, so two regions come out under two keys and one region
// written for two entities does not hand either of them the other's. Deriving
// it from the region rather than drawing it at random is what lets one input
// text be encrypted twice and come out the same, which a reader comparing two
// runs of a tool depends on; the region is already the secret, so a derivation
// from it gives away nothing a holder of the region did not have.
std::string ProtectGeneratedDataKey(std::string_view cleartext,
                                    std::string_view under);

// The text buffer §34.5.27 has an encrypting tool form from the data decryption
// pragma expressions: those written as protect pragma directives, with the key
// on the line beneath the keyword that carries it, encoded under `encoding` as
// §34.5.14 requires of that value.
//
// The two it is formed from here are the two §34.5.14 has a reader take out of
// a key block: the cipher the data block is under, and the key that opens it.
// The subclause admits a wider set and requires none of it -- the buffer is
// formed from any of them -- and the rest of that set is already written in the
// clear beside the block, so a copy sealed inside would tell a reader nothing
// it could not read without the key.
//
// `digest` adds what §34.5.20 stores in a key block beside them: the key that
// opens the region's digests, the cipher §34.5.17 names for it, and the
// algorithm §34.5.21 names for computing them. The key is in the block rather
// than in the clear for the reason the data's own key is -- a key that opens a
// digest is what an alteration would have to be hidden behind, so writing it
// beside the digest would leave the digest vouching for nothing. The two
// identifiers are here because their own subclauses put them here for exactly
// this envelope: each states that it stands in the clear except where a digital
// signature is used, and a region carrying key blocks has one.
//
// It is a buffer of directives rather than of bytes because of what §34.5.27
// has become of it at the other end: the recovered text is parsed to determine
// the keys the data block needs, and the grammar it is parsed by is the one the
// rest of the envelope is written in.
std::string ProtectKeyBlockContent(const ProtectDataDecryption& data,
                                   const ProtectDigestDecryption& digest,
                                   const ProtectEncoding& encoding);

// One key block, written whole: which of the entity's keys it is encrypted
// under, the encoding expression stating how much data it stands for, the
// keyword announcing it, and, on the line after that keyword, `content`
// encrypted under `key` and written in the scheme `encoding` names.
//
// The entity and the designation are restated ahead of each block rather than
// once for the envelope, because §34.4 makes their scope lexical and an
// envelope may carry several blocks under several entities' keys. What stands
// before a block is what a reader combines to reach the key for that block, so
// a block relying on the envelope's last-written pair would be the wrong one
// for every reader but the last.
std::string ProtectKeyBlockDirectives(const ProtectKeyBlockRequest& request,
                                      std::string_view content,
                                      std::string_view key,
                                      const ProtectEncoding& encoding);

// The key blocks `requests` asks for, over the region whose cleartext is
// `cleartext`, using the keys the tool was given.
//
// A request whose designation reaches none of those keys is passed over: there
// is nothing to encrypt its block under, and a block written under no key would
// be a way in that opens onto nothing. Where every request is passed over there
// is no digital signature to produce, and the result is empty throughout.
//
// `digest` is what §34.5.22 has settled about the digests of this region. A
// digest block is owed to each key block produced and follows immediately the
// block it refers to, so the digests are written here rather than gathered up
// afterwards: a reader that has just opened a block finds the digest for that
// block on the next expression rather than having to decide which of several
// digests belongs to it.
ProtectKeyBlocks ProtectKeyBlocksFor(const ProtectKeyBlockRequests& requests,
                                     std::string_view cleartext,
                                     const ProtectKeyList& keys,
                                     const ProtectEncoding& encoding,
                                     const ProtectDigestBlockPolicy& digest);

}  // namespace delta
