#pragma once

#include <string>
#include <string_view>

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

// How this implementation's own encryption is named to whatever reads an
// envelope it produced. The standard reserves identifiers for the ciphers it
// specifies and this is not one of those, so the name is spelled as this
// implementation's own rather than claiming a reserved one. The coding scheme
// the blocks are written in is named the same way, in protect_encoding.h.
inline constexpr std::string_view kEncryptAgent = "deltahdl";
inline constexpr std::string_view kDataMethod = "x-deltahdl-stream";

// What a stretch of source text has said about the keys a protected region is
// under: which key its data are under, and whose keys that one is; and which
// key its digest is under. A key name picks out nothing on its own -- it is a
// member of one entity's list and says nothing outside it -- so a name is read
// and carried beside the entity it is read against rather than alone.
struct RegionKeyNames {
  std::string_view data_keyname;
  std::string_view data_keyowner;
  // §34.5.18 gives the digest a key name of its own, so a region may name one
  // key for its data and another for its digest and the two are carried apart
  // rather than one standing for both.
  std::string_view digest_keyname;
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
};

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
