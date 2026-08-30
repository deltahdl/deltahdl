#pragma once

#include <cstdint>
#include <string>
#include <string_view>

#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_key_block.h"

namespace delta {

// What the lines an encryption envelope is written out of say about the keys
// the region between its delimiters is encrypted under.
//
// §34.4 makes the scope of a protect pragma keyword lexical, so a value written
// ahead of a region is in effect inside it and the value standing where the
// region ends is the one that region's blocks belong to. Every line the reading
// passes is therefore taken for the keywords it writes, and the reading of them
// is in protect_region_lines.cpp.
//
// What that reading gathers is declared here rather than kept to that file
// because the half that encrypts a region reads it: protect_processing.cpp
// settles which key each region is written under, and which key blocks and
// cleartext expressions its envelope carries, from what stands here where the
// region closes.

// A run of source text read for what it says about the keys a region is
// under, together with whether the line just read left a designation to be
// taken from the line after it.
//
// §34.5.26 writes the public key a region's keys are under on the line
// following the keyword announcing it rather than against that keyword, so
// reading that designation spans two lines and the reading has to carry, from
// the first to the second, the fact that it is part way through one.
struct RegionKeyReader {
  RegionKeyNames names;
  // The name the text gave for whoever wrote the design, empty where the text
  // gave none. It is carried beside the names for the reason they are carried
  // at all: §34.5.5 has the expression placed in a directive of the protected
  // envelope rather than encrypted into its block, so it belongs to the
  // description of the envelope rather than to the lines about to stop being
  // readable.
  std::string_view author;
  // What the text offered further about that author, empty where the text
  // offered nothing. It is carried beside the name for the reason the name is
  // carried at all: §34.5.6 has the expression placed in a directive of the
  // protected envelope rather than encrypted into its block, so it belongs to
  // the description of the envelope rather than to the lines about to stop
  // being readable.
  std::string_view author_info;
  // The documentation expressions the text wrote for nothing to interpret, each
  // written back as the directive that carried it and concatenated in the order
  // they were read, empty where the text wrote none.
  //
  // It is carried beside the names for the reason they are carried at all:
  // §34.5.30.2 has the entire comment including the beginning pragma output in
  // cleartext immediately prior to the data block, so it belongs to the
  // description of the envelope rather than to the lines about to stop being
  // readable.
  //
  // It is a string of directives rather than one value because a region may
  // write several and each is owed its own output line. The two names above
  // hold one value apiece and a second directive replaces the first, which is
  // right for a name and wrong here: a region carrying two copyright notices
  // that published only the second would encrypt the first, and being encrypted
  // is what §34.5.30.2 exists to spare such a notice.
  //
  // It is owned rather than a view of the input because it is built here.
  std::string comment_directives;
  // The identifier the text named the algorithm its digests are computed with,
  // empty where the text named none. It is carried beside the names for the
  // reason they are carried at all: §34.5.21 has the identifier unchanged in
  // what an encrypting tool writes out, so it belongs to the description of the
  // envelope rather than to the lines about to stop being readable.
  std::string_view digest_method;
  // The line that naming stands on, carried for the reason data_method_line is:
  // the report about the identifier is made where the region closes, that being
  // where the value in effect for the region is settled, while what the report
  // is about is the expression the author wrote.
  uint32_t digest_method_line = 0;
  // The identifier the text named the cipher its digests are encrypted under,
  // empty where the text named none. It is carried beside the names for the
  // reason they are carried at all: §34.5.17 has the identifier unchanged in
  // the output file, so it belongs to the description of the envelope rather
  // than to the lines about to stop being readable.
  std::string_view digest_key_method;
  // Whether the text asked for a message digest. §34.5.22 makes a digest_block
  // written where no previously generated protected block encloses it a request
  // to generate one in the output file, and §34.4 makes the scope of that
  // request lexical like every other, so it stands from where it was written
  // over everything the reading goes on to reach.
  bool digest_requested = false;
  // The identifier the text named the algorithm its own keys are encrypted
  // under, empty where the text named none. It is carried beside the names for
  // the reason they are carried at all: §34.5.24 has the identifier unchanged
  // in the output file, so it belongs to the description of the envelope rather
  // than to the lines about to stop being readable.
  std::string_view key_method;
  // The line that naming stands on, carried for the reason data_method_line is:
  // the report about the identifier is made where the region closes, and what
  // it is about is the expression the author wrote.
  uint32_t key_method_line = 0;
  // The lines the three names designating a key by name stand on. §34.5.12.2,
  // §34.5.18.2 and §34.5.25.2 each make it an error to write a name the entity
  // in effect beside it holds no key under, and the report about one stands at
  // the line the author wrote it on rather than where the region closes.
  uint32_t data_keyname_line = 0;
  uint32_t digest_keyname_line = 0;
  uint32_t key_keyname_line = 0;
  // The identifier §34.5.11 has the text name the cipher its data are to be
  // encrypted under by, empty where the text named none, and the line the
  // naming stands on. The line is carried because the report is made where the
  // region closes, that being where the value in effect for the region is
  // settled, while what it is about is the expression the author wrote: a
  // report at the closing delimiter would name a line stating no algorithm.
  std::string_view data_method;
  uint32_t data_method_line = 0;
  // The coding scheme in effect where the reading stands, which §34.5.9 has
  // every encoded value of the text written under and §34.5.26 sends the
  // reader of a public key's line to. It is carried with the names because it
  // decides what one of them says: the same line of characters is one key
  // under one scheme and another key, or nothing at all, under another.
  ProtectEncoding encoding = DefaultProtectEncoding();
  // The key blocks §34.5.27 has the text ask for. Each designation of a key of
  // the entity that provided the keys the region's own keys are under asks for
  // one, so a text designating two entities' keys has asked for two ways into
  // the one envelope rather than restating one, and the designations accumulate
  // here instead of replacing one another the way the names above do.
  ProtectKeyBlockRequests key_blocks;
  bool encoded_key_next = false;
  // The same, for §34.5.13's keyword, which announces the line after it in the
  // same way: what is written there is the encoded value of the public key the
  // region's data are to be encrypted under. The two announcements are carried
  // apart because they designate keys of two entities, so a line answering one
  // of them says nothing about the other.
  bool encoded_data_key_next = false;
  // And for §34.5.19's keyword, which announces the line after it the same way
  // again: what is written there is the encoded value of the public key the
  // region's digest is to be encrypted under. It is carried apart from the two
  // above because a region may have its digest under a key of one provider and
  // its data under a key of another, so a line answering one announcement says
  // nothing about the others.
  bool encoded_digest_key_next = false;
};

// The data decryption pragma expressions standing where a region asks for a key
// block. §34.5.27 forms the block's buffer from them and holds every block of
// one envelope to carrying the same ones.
//
// The cipher is this implementation's own rather than whichever one the text
// named, because what §34.5.14 has a reader take out of a key block is the
// cipher the data block it is about to open was really encrypted under, and a
// region is encrypted under this tool's cipher whatever the text asked for.
//
// The key itself is not among them here. The tool has not made one yet at the
// point a region asks for a block, and one key serves every block of a region,
// so it is filled in once the blocks are written rather than carried on each
// request.
ProtectDataDecryption DataDecryptionInEffect(const RegionKeyNames& names);

// The names, entities, algorithms and blocks the walk over an encryption
// envelope's own lines has gathered where it now stands, `contained` saying a
// previously generated begin_protected-end_protected block holds the line.
//
// §34.5.3 leaves the expressions of a contained line uninterpreted, so such a
// line adds nothing and cancels the announcement any keyword left waiting for
// the line beneath it.
void TakeKeyNamesOutsideProtectedBlock(std::string_view line, uint32_t line_num,
                                       bool contained, RegionKeyReader* reader);

}  // namespace delta
