#pragma once

#include <string>
#include <string_view>

#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_key_block.h"

namespace delta {

// The half of envelope encryption that writes: given one encryption envelope as
// the source text spelled it, the decryption envelope that stands in its place.
//
// It is separated from the half that reads a source text for envelopes because
// the two answer different questions. Reading asks what a run of lines says;
// writing asks what an envelope has to state about itself so that whatever
// reads it later needs nothing but the envelope and a key. Neither half looks
// into the other: what passes between them is the envelope below.

// The name §34.5.7 has an encrypting tool identify itself by in each envelope
// it writes. What the value stands for is the tool that performed the
// encryption, so it is this implementation's own name and is settled here
// rather than read out of the text being encrypted: a name that text carried
// was written before this tool reached it and stands for whatever tool it
// passed through then.
inline constexpr std::string_view kEncryptAgent = "deltahdl";

// What §34.5.8 has an encrypting tool offer about itself beyond that name, in
// each envelope it writes. The value holds information the tool performing the
// encryption provides, so it is settled here beside the name rather than read
// out of the text being encrypted: a further word that text carried was offered
// by whatever tool it passed through earlier, and it was offered about that
// tool.
//
// The subclause asks for the expression only where a tool provided one, so a
// tool with nothing further to say about itself writes none. This
// implementation offers what it is, that being the part of it a reader of an
// envelope cannot work out from a name alone.
inline constexpr std::string_view kEncryptAgentInfo =
    "SystemVerilog elaborator and protect envelope writer";

// How this implementation's own encryption is named to whatever reads an
// envelope it produced. The standard reserves identifiers for the ciphers it
// specifies and this is not one of those, so the name is spelled as this
// implementation's own rather than claiming a reserved one. The coding scheme
// the blocks are written in is named the same way, in protect_encoding.h.
inline constexpr std::string_view kDataMethod = "x-deltahdl-stream";

// What a stretch of source text has said about the keys a protected region is
// under: which key its data are under, and whose keys that one is; and which
// key its digest is under. A key name picks out nothing on its own -- it is a
// member of one entity's list and says nothing outside it -- so a name is read
// and carried beside the entity it is read against rather than alone.
struct RegionKeyNames {
  std::string_view data_keyname;
  std::string_view data_keyowner;
  // §34.5.13 lets a region designate the key its data are under by the public
  // key that key is rather than by the name given to it. The two are
  // alternatives and refer to one key wherever a region writes both, so a
  // region that wrote only this one has designated its key as fully as one that
  // wrote the other, and it is read against the entity written beside it just
  // as the name is.
  //
  // This one is the public key itself rather than a view of the text that
  // carried it, because §34.5.13 has that text hold the key's encoded value:
  // the characters the source wrote are one writing of the key under the coding
  // scheme in effect there, and the key is what the designation is.
  std::string data_public_key;
  // §34.5.18 gives the digest a key name of its own, so a region may name one
  // key for its data and another for its digest and the two are carried apart
  // rather than one standing for both.
  std::string_view digest_keyname;
  // §34.5.16 gives the digest an entity of its own to be read against, that
  // subclause permitting a third party's key for the digest distinct from the
  // one behind either the design's author or the tool that encrypted it. A
  // region may therefore name one provider for its data and another for its
  // digest, so the two are carried apart, and the digest's key name is read
  // against this one rather than against the data's.
  std::string_view digest_keyowner;
  // §34.5.19 lets a region designate the key its digest is under by the public
  // key that key is rather than by the name given to it. The two are
  // alternatives and refer to one key wherever a region writes both, so one
  // that wrote only this has designated its digest's key as fully as one that
  // wrote the other, and it is read against the entity the digest names just as
  // that name is.
  //
  // This one is the public key itself rather than a view of the text that
  // carried it, because §34.5.19 has that text hold the key's encoded value:
  // the characters the source wrote are one writing of the key under the coding
  // scheme in effect there, and the key is what the designation is.
  std::string digest_public_key;
  // §34.5.25 gives the region's own keys a third pair of names. A region may
  // state its key this way instead of stating the data's key directly, so the
  // pair is carried beside the other two rather than folded into either: the
  // entity a key name is read against is the one written beside that name.
  std::string_view key_keyname;
  std::string_view key_keyowner;
  // §34.5.26 lets a region designate that same key by the public key it is
  // rather than by the name given to it. The two are alternatives, so a region
  // that wrote only this one has designated its key as fully as one that wrote
  // the other, and it is read against the entity written beside it just as the
  // name is.
  //
  // This one is the public key itself rather than a view of the text that
  // carried it, because §34.5.26 has that text hold the key's encoded value:
  // the characters the source wrote are one writing of the key under the
  // coding scheme in effect there, and the key is what the designation is.
  std::string key_public_key;
};

// One encryption envelope, as the lines of the source text spell it: the
// directive that opened it, the text it enclosed, and the directive that
// closed it. Grouping them mirrors the envelope the standard defines, whose
// two delimiting expressions and enclosed body are one thing rather than three
// unrelated pieces of text.
struct EncryptionEnvelope {
  std::string_view begin_directive;
  std::string_view body;
  std::string_view end_directive;
  // The name the enclosed text gave for whoever wrote the design, empty where
  // the text gave none. It rides on the envelope rather than staying among the
  // body's lines because §34.5.5 has the expression carrying it placed in a
  // directive the envelope encloses and kept out of the data block, and a name
  // left among those lines would go into the block along with them.
  std::string_view author;
  // What the enclosed text offered further about that author, empty where the
  // text offered nothing. It rides on the envelope for the reason the name
  // does: §34.5.6 has the expression carrying it placed in a directive the
  // envelope encloses and kept out of the data block, and a further word left
  // among the body's lines would go into the block along with them.
  std::string_view author_info;
  // What the enclosed text said about the keys it is itself under, each name
  // empty where the text said nothing. They ride on the envelope rather than
  // staying among the body's lines because §34.5.12 has the data's key name
  // written in the clear, §34.5.10 has the entity's name unchanged in what the
  // tool writes out, and §34.5.18 has the digest's key name written in the
  // clear too, while the body is the part of the envelope that stops being
  // readable.
  RegionKeyNames names;
  // The algorithm the enclosed text asked its digests to be computed with. It
  // rides on the envelope for the same reason the names do: §34.5.21 has the
  // identifier unchanged in what the tool writes out, and an identifier left
  // among the body's lines would go into the block along with them.
  std::string_view digest_method;
  // The cipher the enclosed text named for encrypting its digests. It rides on
  // the envelope for the reason the algorithm computing them does: §34.5.17 has
  // the identifier unchanged in the output file, and one left among the body's
  // lines would go into the block along with them.
  std::string_view digest_key_method;
  // The algorithm the enclosed text named for encrypting its own keys. It rides
  // on the envelope for the reason the digest's algorithm does: §34.5.24 has
  // the identifier unchanged in the output file, and one left among the body's
  // lines would go into the block along with them.
  std::string_view key_method;
  // The coding scheme the enclosed text asked its blocks to be written under.
  // §34.5.9 has an encoding pragma expression found in the input specify how
  // the output is encoded, so what a region wrote for itself is what its own
  // blocks are written in, rather than the tool's choice standing over it.
  ProtectEncoding requested_encoding;
};

// How one region is written out: the key its own block is encrypted under, and
// the key blocks carrying that key where §34.5.27 has the envelope carry it.
// The two travel together because a region under a key of the tool's own making
// is unreadable without the blocks that carry it, so writing one without the
// other would leave an envelope nothing can open.
struct RegionEncryption {
  std::string key;
  ProtectKeyBlocks key_blocks;
  // What §34.5.22 has settled about this region's digests: whether the input
  // asked for any, how one is computed, and what one is encrypted with. It
  // travels with the key because a digest is owed to each block the key is used
  // to write, and it follows that block immediately.
  ProtectDigestBlockPolicy digest;
};

// The key an encrypting tool puts one region's digest block under: the one the
// entity that region named for its digest and a designation of one of that
// entity's keys select together out of `keys`.
//
// §34.5.16 has the entity named for the digest select the key that encrypts the
// digest block, and it fills an entity a region left unnamed from the one named
// for the data. A region naming a third party for its digest therefore has that
// party's key encrypt the digest while its data stay under the key their own
// names reach, which is what carrying names of its own gets a digest at all.
//
// The designation is filled the same way for the reason the entity is: a
// reader pairs whichever entity is in effect with whichever designation is, so
// a writer pairing them any other way would seal a digest that reader cannot
// open.
//
// Two designations reach a key here, and they are alternatives to one another:
// the name §34.5.18 gives that key, and the public key §34.5.19 says it is.
// The name is tried first, a region writing both having picked out one key
// twice, and the public key is tried where the name reaches nothing rather
// than instead of it, so a region designating its digest's key only that way
// is served as fully as one that named it. Each falls back to the
// corresponding designation the region's data carry, which is where the two
// subclauses send a region that wrote neither.
//
// The result is empty where the pair reaches none of the keys held, which is
// where a region naming neither an entity nor a key for its digest ends up:
// there is no key of the digest's own then, and a caller falls back to whatever
// the subclauses defining those two names settle.
std::string_view RegionDigestKey(const RegionKeyNames& names,
                                 const ProtectKeyList& keys);

// The scheme the blocks of one envelope are written under: the one the
// enclosed text asked for, where a block of that scheme can be carried on the
// expression a block is written on, and this implementation's own otherwise.
//
// A line length the text stated is not carried across. It is a maximum on the
// characters of a line of the block, and a block written as the value of a
// pragma expression is written on the directive's own line, so a break put in
// to honor the maximum would end the directive rather than the line.
ProtectEncoding EnvelopeBlockEncoding(const ProtectEncoding& requested);

// The decryption envelope one encryption envelope is transformed into: the
// pair of expressions that delimits a protected region, with the encrypted
// body recorded on an expression between them. The region's own text does not
// appear.
//
// The delimiting directives are the encryption envelope's own, each carrying
// the expressions that specified it, with the delimiter itself transformed.
// The expressions specifying the encryption envelope therefore become the
// expressions specifying the decryption envelope: those ahead of the opening
// delimiter describe the new envelope, and those the enclosed text held were
// encrypted along with it.
//
// The keywords describing how the envelope was made are written inside it,
// ahead of the encrypted body, so they are content expressions of the envelope
// and each one is in effect where the block depending on it is read. A reset
// follows the whole of it. Both come from §34.4: an envelope that carries its
// own description is read the same way wherever it is placed, and the reset
// keeps that description from standing over whatever the text goes on to hold.
std::string DecryptionEnvelopeText(const EncryptionEnvelope& envelope,
                                   const RegionEncryption& how);

}  // namespace delta
