#include "preprocessor/protect_processing.h"

#include <cctype>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_input_line.h"
#include "preprocessor/protect_key_block.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_pragma_line.h"

namespace delta {
namespace {

// How a region's cleartext becomes the bytes a block records, and those bytes
// the cleartext again, is written in protect_processing_cipher.cpp. What one
// line of a source text says -- which protect pragma keywords it names, and how
// -- is answered in protect_pragma_line.cpp. Where one line of an encrypting
// tool's input stands, and what §34.5 makes an error in it, is answered in
// protect_input_line.cpp. What the envelope taking a region's place says is
// written in protect_envelope_output.cpp. What this file does is read a source
// text for the regions it delimits and settle which key each of them is written
// under; the other four are reached through the declarations they share.

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
  // The identifier the text named the algorithm its digests are computed with,
  // empty where the text named none. It is carried beside the names for the
  // reason they are carried at all: §34.5.21 has the identifier unchanged in
  // what an encrypting tool writes out, so it belongs to the description of the
  // envelope rather than to the lines about to stop being readable.
  std::string_view digest_method;
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
ProtectDataDecryption DataDecryptionInEffect(const RegionKeyNames& names) {
  ProtectDataDecryption data;
  data.method = kDataMethod;
  data.keyname = ProtectPragmaValueBody(names.data_keyname);
  return data;
}

// The identifiers a line names for the algorithms a region's blocks are
// produced and opened with, each taken the way the names beside them are: the
// value standing where a region ends is the one that region's blocks belong to,
// and a line writing none of them leaves the earlier ones as they were.
void TakeMethodKeywords(std::string_view line, RegionKeyReader* reader) {
  // §34.5.21 puts the identifier in effect for the blocks written after it, so
  // the value standing where a region ends is the one that region's digests
  // belong to.
  std::string_view digest_method =
      KeywordValueOnLine(line, kDigestMethodKeyword);
  if (!digest_method.empty()) reader->digest_method = digest_method;
  // §34.5.17 names the cipher those digests are encrypted under, which is a
  // separate identifier from the one computing them: a digest is computed and
  // then put under a key, and neither step says anything about the other.
  std::string_view digest_key_method =
      KeywordValueOnLine(line, kDigestKeyMethodKeyword);
  if (!digest_key_method.empty()) reader->digest_key_method = digest_key_method;
  // §34.5.24 names the algorithm the region's own keys are encrypted under, and
  // the reading takes it the same way.
  std::string_view key_method = KeywordValueOnLine(line, kKeyMethodKeyword);
  if (!key_method.empty()) reader->key_method = key_method;
}

// Takes from `line` whatever it says about the keys a region is under. What is
// in effect where a region ends is the last writing of each name, so a later
// expression replaces an earlier one and a line writing none of them leaves
// them all as they were.
//
// A line the previous one announced a public key on is that key's encoded
// value and nothing else: §34.5.26 gives the whole of that line to the value,
// so it is taken as written -- without the whitespace that positioned it --
// rather than searched for expressions it cannot be carrying.
//
// What that line carries is the key's encoded value rather than the key, and
// §34.5.26 sends the reading to the encoding pragma expression in effect for
// the scheme it was encoded under. Reading it back out is what leaves the key
// itself in hand, so a text writing one key under two schemes has written one
// designation twice rather than two. A line that is not something the scheme
// in effect writes carries no key, and the region is left designating none.
void TakeKeyPublicKeyLine(std::string_view line, uint32_t line_num,
                          RegionKeyReader* reader) {
  reader->encoded_key_next = false;
  std::string key;
  // The reading goes through the same step every encoded value of an envelope
  // goes through, so a scheme this tool has none of and a line that scheme
  // never wrote leave the region designating nothing in the same way. There is
  // nothing here to report either to: what a tool encrypting a text can do
  // about a designation it cannot read is leave the text designating no key,
  // which is what a text writing none would have left as well.
  if (ReadProtectEncodedValue(TrimTrailing(TrimLeading(line)), reader->encoding,
                              &key) != ProtectEncodedValueRead::kRead) {
    return;
  }
  reader->names.key_public_key = std::move(key);
  // §34.5.27 owes a key block to each key the text designates for the region's
  // own keys, and §34.5.26 makes this designation an alternative spelling of
  // the one written against a keyword rather than a lesser one, so a line
  // carrying it asks for a block exactly as that keyword does.
  //
  // The block is recorded as asked for here rather than on the keyword's own
  // line, that keyword having designated nothing until the value beneath it was
  // read: a line the scheme in effect never wrote leaves the region designating
  // no key at all and asks for no block.
  reader->key_blocks.DesignatePublicKey(
      reader->names.key_keyowner, reader->names.key_public_key,
      DataDecryptionInEffect(reader->names), line_num);
}

// A line the previous one announced the data's public key on is that key's
// encoded value and nothing else: §34.5.13 gives the whole of that line to the
// value, so it is taken as written -- without the whitespace that positioned it
// -- rather than searched for expressions it cannot be carrying.
//
// What that line carries is the key's encoded value rather than the key, and
// §34.5.13 sends the reading to the encoding pragma expression currently in
// effect for the scheme it was encoded under. Reading it back out is what
// leaves the key itself in hand, so a text writing one key under two schemes
// has written one designation twice rather than two. A line that is not
// something the scheme in effect writes carries no key, and the region is left
// designating none: what an encrypting tool can do about a designation it
// cannot read is leave the text designating no key, which is where a text
// writing none would have left it as well.
void TakeDataPublicKeyLine(std::string_view line, RegionKeyReader* reader) {
  reader->encoded_data_key_next = false;
  std::string key;
  if (ReadProtectEncodedValue(TrimTrailing(TrimLeading(line)), reader->encoding,
                              &key) != ProtectEncodedValueRead::kRead) {
    return;
  }
  reader->names.data_public_key = std::move(key);
}

// A line the previous one announced the digest's public key on is that key's
// encoded value and nothing else: §34.5.19 gives the whole of that line to the
// value, so it is taken as written -- without the whitespace that positioned it
// -- rather than searched for expressions it cannot be carrying.
//
// What that line carries is the key's encoded value rather than the key, and
// §34.5.19 sends the reading to the encoding pragma expression currently in
// effect for the scheme it was encoded under. Reading it back out is what
// leaves the key itself in hand, so a text writing one key under two schemes
// has written one designation twice rather than two. A line that is not
// something the scheme in effect writes carries no key, and the region is left
// designating none for its digest: what an encrypting tool can do about a
// designation it cannot read is leave the text designating no key, which is
// where a text writing none would have left it as well.
void TakeDigestPublicKeyLine(std::string_view line, RegionKeyReader* reader) {
  reader->encoded_digest_key_next = false;
  std::string key;
  if (ReadProtectEncodedValue(TrimTrailing(TrimLeading(line)), reader->encoding,
                              &key) != ProtectEncodedValueRead::kRead) {
    return;
  }
  reader->names.digest_public_key = std::move(key);
}

// §34.5.9 puts the coding scheme in effect wherever the expression naming it
// was written, so a text may state one scheme for one region and another for
// the next, and a region is read for whichever of them it wrote between its own
// delimiters.
//
// §34.5.9.1 writes the scheme outside the brackets that make the other two
// subkeywords optional, so a value naming no scheme is not this keyword's value
// at all. Such a value settles nothing, which is a different thing from
// settling emptiness: a region that named a scheme on an earlier line still
// wants it, and an expression asking for nothing has no standing to take away
// what an earlier one asked for. Reading it as a request would leave the region
// encrypted under this tool's own writing while its text plainly named another.
void TakeEncodingKeyword(std::string_view line, RegionKeyReader* reader) {
  std::string_view written = KeywordValueOnLine(line, kEncodingKeyword);
  if (written.empty()) return;
  ProtectEncoding stated = ParseProtectEncoding(written);
  if (stated.enctype.empty()) return;
  reader->encoding = stated;
}

// Whether `line` carried the encoded value a keyword on the line before it left
// waiting. Three keywords each give the line beneath them to a public key, so
// the line after one of them is that key's characters rather than a line of
// expressions to be read for keywords of its own.
bool TookAwaitedPublicKey(std::string_view line, uint32_t line_num,
                          RegionKeyReader* reader) {
  if (reader->encoded_key_next) {
    TakeKeyPublicKeyLine(line, line_num, reader);
    return true;
  }
  if (reader->encoded_data_key_next) {
    TakeDataPublicKeyLine(line, reader);
    return true;
  }
  if (reader->encoded_digest_key_next) {
    TakeDigestPublicKeyLine(line, reader);
    return true;
  }
  return false;
}

// What §34.5.5 and §34.5.6 say about whoever wrote the design, and the encoding
// the region states for itself.
//
// Each is taken the way the designations below are: the value standing where a
// region ends is the one that region's envelope carries, and a line writing
// none leaves the earlier one as it was. §34.5.5.1 and §34.5.6.1 both write the
// value as a string, which is one written thing, so a parenthesized list of
// further expressions is not the value either keyword is defined with. Taking
// one would put a list of somebody's subkeywords where a person's name belongs,
// and publish it in the clear on the envelope.
void TakeAuthorship(std::string_view line, RegionKeyReader* reader) {
  std::string_view author = KeywordSingleValueOnLine(line, kAuthorKeyword);
  if (!author.empty()) reader->author = author;
  std::string_view author_info =
      KeywordSingleValueOnLine(line, kAuthorInfoKeyword);
  if (!author_info.empty()) reader->author_info = author_info;
  TakeEncodingKeyword(line, reader);
}

// The names a line designates the region's keys by: the data key and the entity
// that provided it, the digest key and its own entity, and the key the region
// designates for keys of its own.
void TakeKeyDesignations(std::string_view line, uint32_t line_num,
                         RegionKeyReader* reader) {
  RegionKeyNames* names = &reader->names;
  std::string_view keyname = KeywordValueOnLine(line, kDataKeynameKeyword);
  if (!keyname.empty()) names->data_keyname = keyname;
  // §34.5.10.1 writes the value as a string, which is one written thing, so a
  // parenthesized list of further expressions is not the value this keyword is
  // defined with. Taking one would put a list of somebody's subkeywords where
  // the name of the entity that provided the region's keys belongs, and then
  // write it on the envelope in the clear, quoted as though it were that name.
  std::string_view keyowner =
      KeywordSingleValueOnLine(line, kDataKeyownerKeyword);
  if (!keyowner.empty()) names->data_keyowner = keyowner;
  // §34.5.18.1 writes the value as a string, which is one written thing, so a
  // parenthesized list of further expressions is not the value this keyword is
  // defined with. Taking one would put a list of somebody's subkeywords where
  // the name of the key a region's digest is under belongs, and §34.5.18.2 has
  // that name written onto the envelope in the clear, so the list would go out
  // quoted as though it were the name.
  std::string_view digest =
      KeywordSingleValueOnLine(line, kDigestKeynameKeyword);
  if (!digest.empty()) names->digest_keyname = digest;
  // §34.5.16 names the entity that provided the key the digest is under, which
  // the digest's own key name is read against rather than the data's entity.
  std::string_view provider = KeywordValueOnLine(line, kDigestKeyownerKeyword);
  if (!provider.empty()) names->digest_keyowner = provider;
  std::string_view key_name = KeywordValueOnLine(line, kKeyKeynameKeyword);
  std::string_view key_owner = KeywordValueOnLine(line, kKeyKeyownerKeyword);
  if (!key_owner.empty()) names->key_keyowner = key_owner;
  // §34.5.27 owes a key block to each key the text designates for the region's
  // own keys, so the designation is recorded as a request beside being kept as
  // the name in effect. The entity it is read against is the one standing here,
  // which is why the request is made once the line has been read whole rather
  // than where the name itself was taken.
  if (!key_name.empty()) {
    names->key_keyname = key_name;
    reader->key_blocks.Designate(names->key_keyowner, key_name,
                                 DataDecryptionInEffect(*names), line_num);
  }
}

// What a line announces about the lines after it, and the one block it can ask
// the output for.
void TakeAnnouncements(std::string_view line, RegionKeyReader* reader) {
  // §34.5.22 makes a digest_block written here a request to generate a message
  // digest in the output file. This line is outside every previously generated
  // protected block -- the reading passes over those without interpreting what
  // they hold -- so a block named here belongs to no earlier encryption and is
  // the request rather than a digest some other tool already produced.
  if (NamesKeyword(line, kDigestBlockKeyword)) reader->digest_requested = true;
  reader->encoded_key_next = NamesBareKeyword(line, kKeyPublicKeyKeyword);
  // §34.5.13 defines its keyword standing alone and gives the line after it to
  // the encoded value of the public key the data are to be encrypted under, so
  // a line naming it in that spelling leaves the designation to be taken from
  // the line below. The same name carrying a pragma_value is the keyword
  // written in a spelling it is not defined with and announces nothing about
  // the line beneath it.
  reader->encoded_data_key_next = NamesBareKeyword(line, kDataPublicKeyKeyword);
  // §34.5.19 defines its keyword the same way, and gives the line after it to
  // the encoded value of the public key the region's digest is to be encrypted
  // under. The same name carrying a pragma_value is the keyword written in a
  // spelling it is not defined with, and announces nothing about the line
  // beneath it.
  reader->encoded_digest_key_next =
      NamesBareKeyword(line, kDigestPublicKeyKeyword);
}

void TakeKeyNames(std::string_view line, uint32_t line_num,
                  RegionKeyReader* reader) {
  if (TookAwaitedPublicKey(line, line_num, reader)) return;
  TakeAuthorship(line, reader);
  TakeKeyDesignations(line, line_num, reader);
  TakeMethodKeywords(line, reader);
  TakeAnnouncements(line, reader);
}

// The same, for a line whose place in the input has already been settled.
// `contained` says a previously generated protected block holds the line, and
// §34.5.3 leaves the expressions of such a line uninterpreted: they describe
// an envelope some earlier encryption produced, so none of them is allowed to
// displace what the encryption now in process has in effect.
//
// A keyword left waiting for the line beneath it is answered here rather than
// carried over the block. Three of the keywords above leave the reading part
// way through a designation, the value being written on the next line, and a
// next line that a block contains is one the designation's value was never
// written on: those characters belong to a model somebody sealed already.
//
// Both other ways of treating them let the block decide what the current
// encryption is under, which is the corruption §34.5.3 rules out. Reading them
// as the value would interpret the block's content outright. Leaving the
// keyword waiting would carry the announcement past the block and spend it on
// the first line after it -- a line of the enclosing region's own text, which
// the author wrote as design rather than as a key.
//
// So the designation reaches nothing, which is where a designation whose line
// carried nothing the scheme in effect writes is left as well. A region is then
// under whatever else it named, and under no key at all where it named nothing
// else: a region there is nothing to encrypt, rather than one sealed under a
// key that was never designated for it.
void TakeKeyNamesOutsideProtectedBlock(std::string_view line, uint32_t line_num,
                                       bool contained,
                                       RegionKeyReader* reader) {
  if (!contained) {
    TakeKeyNames(line, line_num, reader);
    return;
  }
  reader->encoded_key_next = false;
  reader->encoded_data_key_next = false;
  reader->encoded_digest_key_next = false;
}

// One encryption envelope as it is read, line by line: the directive that
// opened it in both spellings needed -- as the source wrote it, and as the
// envelope taking its place will carry it -- the text read since, and what
// that text said about the key its own data are under.
struct ReadRegion {
  std::string_view opening_line;
  std::string opening_directive;
  // Every line the region enclosed, as the source wrote it. A region there is
  // nothing to encrypt goes back exactly as it stands, so what goes back is
  // this rather than what a block would have recorded.
  std::string source_body;
  // The part of that text a block records. §34.5.5 keeps the author's name out
  // of it and §34.5.6 keeps out whatever further that author offered, both
  // being written in the clear inside the envelope instead, so a directive
  // carrying either is held back from here.
  std::string body;
  RegionKeyReader written_inside;
};

// Whether one line of an encryption envelope's enclosed text carries one of the
// two expressions describing the design's author: the one §34.5.5 names them
// with, and the one §34.5.6 offers anything further about them on.
//
// It is the spelling §34.5.5.1 and §34.5.6.1 define that counts: the keyword
// with a string written against it. Either keyword standing alone describes
// nobody, and so does either carrying a parenthesized list of further
// expressions, a list being something other than the one written thing a string
// is. Neither subclause says anything about those spellings, so §34.5.1's rule
// for everything else between the delimiters is what governs -- the line goes
// into the block along with the rest.
//
// The two questions this file asks about each expression -- whether the line
// carries it, and what it says -- are asked of the same spelling, so a line
// held back from the block is a line whose value the envelope goes on to carry.
// Were one of them to admit a spelling the other turned away, a line would be
// kept out of the block on account of a value that never reached the envelope,
// and the design would lose it in both directions at once.
//
// A line a previously generated protected block contains carries nothing of the
// kind either. §34.5.3 leaves the expressions of such a line uninterpreted and
// §34.5.1 has that block travel into the larger envelope as the bytes it is
// written with, so an expression written there describes the author of a design
// some earlier encryption sealed rather than the author of this one.
bool CarriesAuthorDescription(std::string_view line,
                              bool previously_protected) {
  if (previously_protected) return false;
  return !KeywordSingleValueOnLine(line, kAuthorKeyword).empty() ||
         !KeywordSingleValueOnLine(line, kAuthorInfoKeyword).empty();
}

// Adds one line of enclosed text to the region being read: to the text that
// goes back where the region cannot be encrypted, to the text a block records
// unless §34.5.5 or §34.5.6 holds it back from there, and to what the region
// has said about itself.
void AppendEnvelopeLine(std::string_view line, uint32_t line_num,
                        bool previously_protected, ReadRegion* region) {
  region->source_body.append(line);
  if (!CarriesAuthorDescription(line, previously_protected)) {
    region->body.append(line);
  }
  // What the region itself wrote is kept apart from what is merely in effect
  // over it: those are the expressions the envelope has to carry in the clear,
  // the rest of the region's text being about to stop being readable. One
  // written outside the region is in the output already.
  TakeKeyNamesOutsideProtectedBlock(line, line_num, previously_protected,
                                    &region->written_inside);
}

// The key one region's data are encrypted under. §34.5.10 has the entity a
// region names select it out of the keys supplied under the names that select
// them, so two regions naming two entities are encrypted under two keys.
//
// A user who supplied keys under no names at all supplied one key for every
// region, whoever a region names, and that key is what every region is
// encrypted under. That is the whole of what a user holding one key needs to
// say, which is why it is not the same thing as a list holding one entry.
//
// The names a region writes for its own keys reach no key here. §34.5.27 has
// those name the key a key block is encrypted under, and a region carrying one
// has asked for the arrangement below, in which the block its data are under is
// under a key of the tool's own making instead. Reading them here as well would
// leave the region encrypted under the key that opens its key block, which is
// the one key that block was written to keep out of the clear.
// §34.5.13 gives the region a second way to pick that key out: the public key
// it is, written beneath the keyword announcing it rather than against a name.
// It is an alternative to the name given to the key rather than a companion of
// it -- a region writing both has picked out one key twice -- so it is tried
// where the name reaches nothing rather than instead of the name, and a region
// writing only this one designates its key as fully as one writing only the
// other.
std::string_view RegionKey(const RegionKeyNames& names,
                           std::string_view exchange_key,
                           const ProtectKeyList& keys) {
  if (keys.Empty()) return exchange_key;
  std::string_view owner = ProtectPragmaValueBody(names.data_keyowner);
  std::string_view under_name =
      keys.KeyFor(owner, ProtectPragmaValueBody(names.data_keyname));
  if (!under_name.empty()) return under_name;
  return keys.KeyFor(owner, names.data_public_key);
}

// The key block a region asks for by what stands in effect over it rather than
// by what it writes between its own delimiters.
//
// §34.4 makes the scope of a designation lexical, so one written ahead of a
// region designates a key for that region as much as one written inside it, and
// a region that wrote none of its own has not thereby asked for nothing. It is
// consulted only where the region wrote none, because a region that did write
// its own said which readers this envelope is for.
//
// `closing_line` is the 1-based line the region's closing expression stands on,
// and it is what the one request this can produce records. The designation
// itself was written ahead of the region, where it stood for whichever region
// closed next rather than for this one, so where it asks for a block is where
// this region ends. Nothing reads the line off a lone request either way:
// §34.5.27's requirement is one two blocks can break and one cannot.
ProtectKeyBlockRequests DesignatedKeyBlocks(const RegionKeyNames& names,
                                            uint32_t closing_line) {
  ProtectKeyBlockRequests requests;
  if (!names.key_keyname.empty()) {
    requests.Designate(names.key_keyowner, names.key_keyname,
                       DataDecryptionInEffect(names), closing_line);
  } else if (!names.key_public_key.empty()) {
    requests.DesignatePublicKey(names.key_keyowner, names.key_public_key,
                                DataDecryptionInEffect(names), closing_line);
  }
  return requests;
}

// Which of the two arrangements a region is written under, decided by what the
// region said about its keys.
//
// A region whose data name a key the tool holds said outright what its data are
// under, so its block stays under that key and it carries no key of its own.
// Where the data name no such key, §34.5.27's arrangement is the one the region
// asked for: the tool makes a key for the region, and every key block that
// region designated a reader for carries that made key. A region that
// designated no reader the tool holds a key for is left with neither, which is
// a region there is nothing to encrypt.
// What §34.5.22 has settled about a region's digests by the time the region
// closes, apart from the key, which is not known until the region's own key is.
//
// Each part is read where the region ends rather than where the region opens,
// the scope of every one of these keywords being lexical: an expression written
// inside the region is as much in effect for it as one written ahead of it, and
// the value standing at the end is the one the region's blocks belong to.
ProtectDigestBlockPolicy DigestPolicyFor(const RegionKeyReader& in_effect) {
  ProtectDigestBlockPolicy policy;
  policy.requested = in_effect.digest_requested;
  // §34.5.22 has the digest generated under the algorithm the digest_method
  // pragma expression specifies, which is that keyword's default where the text
  // named none.
  policy.method =
      in_effect.digest_method.empty()
          ? std::string(kDefaultDigestMethod)
          : std::string(ProtectPragmaValueBody(in_effect.digest_method));
  // §34.5.21 has that identifier unchanged wherever it is written out, and the
  // key block of a signed region is one of the places it is written. It is kept
  // as the source spelled it, and left empty where the source spelled nothing:
  // the default filling the field above is this implementation's and not the
  // author's, so a block claiming the author wrote it would be claiming
  // something the text never said.
  policy.stated_method = std::string(in_effect.digest_method);
  // §34.5.22 has the digest then encrypted under the cipher digest_key_method
  // names, and §34.5.17 fills that place from the cipher the region's data are
  // under where the text named none. The envelope this tool writes states its
  // own cipher for the data, so leaving the identifier empty is what sends a
  // reader to it rather than to whichever cipher the input happened to name.
  //
  // It is the pragma_value as the source wrote it, quotes and all where it had
  // them, because §34.5.17 has the identifier unchanged wherever it is written
  // out and a value written bare that came back in quotes has been changed.
  policy.key_method = std::string(in_effect.digest_key_method);
  return policy;
}

RegionEncryption RegionEncryptionFor(const RegionKeyReader& in_effect,
                                     const ReadRegion& region,
                                     std::string_view exchange_key,
                                     const ProtectKeyList& keys,
                                     uint32_t closing_line) {
  RegionEncryption how;
  how.digest = DigestPolicyFor(in_effect);
  std::string_view named = RegionKey(in_effect.names, exchange_key, keys);
  if (!named.empty()) {
    how.key = named;
    // §34.5.16 has the entity a region named for its digest select the key
    // encrypting the digest block, so a region naming one whose key the tool
    // holds puts its digest under that key. Where those names reach none,
    // §34.5.20 fills the place from the key the data are under: such a region
    // carries no key block for a digest key of its own to travel in.
    std::string_view own = RegionDigestKey(in_effect.names, keys);
    how.digest.key = own.empty() ? named : own;
    return how;
  }
  ProtectKeyBlockRequests requests =
      region.written_inside.key_blocks.Empty()
          ? DesignatedKeyBlocks(in_effect.names, closing_line)
          : region.written_inside.key_blocks;
  how.key_blocks = ProtectKeyBlocksFor(
      requests, region.body, keys,
      EnvelopeBlockEncoding(region.written_inside.encoding), how.digest);
  how.key = how.key_blocks.data_key;
  // A region whose keys travel in key blocks has a key of its own for its
  // digests, made beside them and carried in the same blocks, so the digest of
  // its data block is under that key rather than under the data's.
  how.digest.key = how.key_blocks.digest_key;
  return how;
}

// The text an encryption envelope leaves behind once the directive closing it
// has been read.
//
// A region with a key to be encrypted under becomes the decryption envelope
// standing in its place. A region left without one -- the entity it names
// having supplied no key to this tool -- is not transformed at all: there is
// nothing to encrypt it under, so the directives that delimited it and the
// text between them go back exactly as the source wrote them, rather than as
// an envelope whose block stands for nothing.
std::string ClosedRegionText(const ReadRegion& region,
                             const RegionKeyReader& in_effect,
                             std::string_view line,
                             const DelimiterMatch& delimiter,
                             const RegionEncryption& how) {
  if (how.key.empty()) {
    std::string text(region.opening_line);
    text.append(region.source_body).append(line);
    return text;
  }
  // §34.5.2.2 has the expression that closed the region replaced, in what the
  // encrypting tool writes out, by the one §34.5.4 defines. It is the word that
  // is replaced and not the directive carrying it, so the line goes through the
  // same transformation the opening one did and every expression written beside
  // the word is carried on to describe the envelope standing in the region's
  // place.
  std::string closing_directive =
      TransformedDelimiterLine(line, delimiter, kEndDecryptionKeyword);
  EncryptionEnvelope envelope;
  envelope.begin_directive = region.opening_directive;
  envelope.body = region.body;
  envelope.end_directive = closing_directive;
  // §34.5.5 asks for the expression present in the encryption envelope, so it
  // is taken from what the region wrote between its own delimiters rather than
  // from what merely stands in effect over it. An expression written outside
  // the region has its own treatment there: it is copied into the output stream
  // unchanged, which is what carrying the text across as its own bytes does,
  // and lifting it into the envelope as well would write it out twice.
  envelope.author = region.written_inside.author;
  // §34.5.6 asks the same of whatever further the region offered about that
  // author, and it is taken from the same place for the same reason: the
  // subclause asks for the expression present in the encryption envelope, and
  // one written outside the region already has its own treatment there -- it is
  // copied into the output stream unchanged where it stands.
  envelope.author_info = region.written_inside.author_info;
  envelope.names = region.written_inside.names;
  // §34.5.13 asks for this one designation in each protected block it was used
  // for, so it is taken from what stands in effect where the region closes
  // rather than from what the region wrote between its own delimiters.
  //
  // The two differ where an expression ahead of the region designated the key,
  // which §34.4's lexical scope makes as much this region's designation as one
  // written inside it. Left to what the region restated, such a block would say
  // nothing about the key that opens it: a reader reaching the envelope on its
  // own, or reaching it after the keywords have been put back to their
  // defaults, would have nowhere to learn the designation from. The names
  // beside it are governed by subclauses that ask only for their values
  // unchanged in the output, so they are left as they were.
  envelope.names.data_public_key = in_effect.names.data_public_key;
  // §34.5.19 asks the same of the designation a region wrote for its digest's
  // key, and for the same reason: a block relying on a designation made ahead
  // of the region would say nothing about the key its digest is under, so a
  // reader reaching the envelope on its own would have nowhere to learn it
  // from.
  envelope.names.digest_public_key = in_effect.names.digest_public_key;
  envelope.digest_method = region.written_inside.digest_method;
  envelope.digest_key_method = region.written_inside.digest_key_method;
  envelope.key_method = region.written_inside.key_method;
  envelope.requested_encoding = region.written_inside.encoding;
  return DecryptionEnvelopeText(envelope, how);
}

}  // namespace

std::string EncryptEnvelopes(std::string_view source_text,
                             std::string_view exchange_key,
                             const ProtectKeyList& keys, DiagEngine* diag,
                             uint32_t file_id) {
  // With neither a key of one's own nor keys supplied under the names that
  // select them, there is nothing any region could be encrypted under, so the
  // text stands as it is written.
  //
  // What a caller holding an engine is still owed is the reading. §34.5.1
  // makes a region opened inside an open one an error in the text itself, and a
  // text carries that error whether or not a key was supplied to act on it, so
  // a caller that can report is told rather than handed its text back in
  // silence. Skipping the reading here would leave an author who ran this half
  // without a key unable to tell an input that was well formed from one nothing
  // looked at.
  //
  // The text is the same either way. A region reaching no key is not
  // transformed at all -- its delimiters and the lines between them go back as
  // the source wrote them -- and every line outside a region is carried across
  // as its own bytes, so reading a keyless text through returns exactly what
  // was handed in. The shortcut is kept for the caller with nowhere to report
  // to, which is the caller it saves the reading for.
  if (diag == nullptr && exchange_key.empty() && keys.Empty()) {
    return std::string(source_text);
  }
  std::string transformed;
  ReadRegion region;
  // What the text read so far has said about the key the data are under. The
  // scope of a protect pragma keyword is lexical, so a name written before a
  // region is as much in effect inside it as one written between its
  // delimiters, and it is the value standing where a region ends that selects
  // the key that region is encrypted under.
  RegionKeyReader in_effect;
  // Where the reading stands with respect to the models this text has sealed
  // inside it already. §34.5.3 has the lines of one of those read as cleartext
  // rather than as description, so this is consulted ahead of everything the
  // reading does with a line.
  PreviouslyProtectedBlock previously_protected;
  bool in_envelope = false;
  // Which line of the input the reading stands on, counted from one as the
  // reports name it. A report about a line of a source description carries the
  // position of that line, and the only thing that knows where a line stood in
  // the text is the walk that split the text into lines.
  uint32_t line_num = 0;
  for (std::string_view line : SplitLines(source_text)) {
    ++line_num;
    SourceLoc loc = LineOf(file_id, line_num);
    InputLine input = ReadInputLine(line, &previously_protected, diag, loc);
    TakeKeyNamesOutsideProtectedBlock(line, line_num,
                                      input.previously_protected, &in_effect);
    DelimiterMatch delimiter = input.delimiter;
    // §34.5.2.2 has the closing expression state, in the input cleartext, where
    // the region that is to be encrypted stops. The region therefore ends at
    // the line the word is written on rather than at the end of the text or at
    // some later delimiter, so this is where the lines gathered so far become a
    // block and the lines after it go back to being carried across.
    if (in_envelope && delimiter.kind == EnvelopeDelimiter::kEnd) {
      RegionEncryption how =
          RegionEncryptionFor(in_effect, region, exchange_key, keys, line_num);
      // §34.5.27 has every key block of one envelope encode the same data
      // decryption key data, so a region whose data decryption pragma
      // expressions changed value between two of them is reported rather than
      // left carrying blocks that open onto different accounts of one key. The
      // report stands at the block that stopped agreeing rather than here,
      // where the region merely closed.
      if (diag != nullptr && how.key_blocks.data_changed_line != 0) {
        diag->Error(
            LineOf(file_id, how.key_blocks.data_changed_line),
            "protect pragma data decryption expressions change value between "
            "the key_block pragma expressions of one encryption envelope",
            Subclause("34.5.27"));
      }
      transformed.append(
          ClosedRegionText(region, in_effect, line, delimiter, how));
      in_envelope = false;
    } else if (in_envelope) {
      // §34.5.1 rules out a second opening expression here, this region not
      // having been closed yet, so a line carrying one is reported before it is
      // taken as text of the region.
      ReportNestedRegion(delimiter, diag, loc);
      // §34.5.3 and §34.5.4 have the two expressions delimiting a previously
      // generated block, and everything between them, encrypted into the block
      // of the envelope enclosing them. Adding the line unread is what does
      // that: an already-protected model travels into the larger one as the
      // bytes it is written with.
      AppendEnvelopeLine(line, line_num, input.previously_protected, &region);
    } else if (delimiter.kind == EnvelopeDelimiter::kBegin) {
      in_envelope = true;
      region.opening_line = line;
      region.opening_directive =
          TransformedDelimiterLine(line, delimiter, kBeginDecryptionKeyword);
      region.source_body.clear();
      region.body.clear();
      region.written_inside = {};
      // What the region wrote for itself is collected apart from what stands
      // over it, but the coding scheme is not one of the things collected: it
      // decides how the region's own lines are read, and the scheme in effect
      // where the region opens is in effect inside it until the region says
      // otherwise.
      region.written_inside.encoding = in_effect.encoding;
    } else {
      // Text no encryption envelope contains is carried across as the bytes it
      // was written with, whatever it says.
      transformed.append(line);
    }
  }
  // A region whose closing expression was never written closes no envelope, so
  // nothing was replaced: the opening directive and the lines after it are
  // text of the source like any other, and go back as they stand.
  if (in_envelope) {
    transformed.append(region.opening_line);
    transformed.append(region.source_body);
  }
  return transformed;
}

}  // namespace delta
