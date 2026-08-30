// The reading of the lines an encryption envelope is written out of, which
// settles what the region between its delimiters is encrypted under.
//
// §34.4 gives every protect pragma keyword a lexical scope, so a value written
// ahead of a region is in effect inside it and the value standing where the
// region ends is the one the region's blocks belong to. Every line the walk
// reaches is therefore read for the keywords it writes: §34.5.5, §34.5.6 and
// §34.5.30 name what the envelope publishes in the clear, §34.5.10, §34.5.12,
// §34.5.16, §34.5.18, §34.5.23 and §34.5.25 designate the keys, §34.5.11,
// §34.5.17, §34.5.21 and §34.5.24 name the algorithms, §34.5.9 names the
// coding scheme, §34.5.22 asks for a message digest, §34.5.27 asks for a key
// block and §34.5.31 puts them all back to their defaults.
//
// §34.5.13, §34.5.19 and §34.5.26 each define their keyword as the
// pragma_keyword standing alone and put the encoded public key it designates on
// the line beneath, so three of the readings here span two lines rather than
// one.
//
// What the walk gathers is read by protect_processing.cpp, which finds the
// regions a source text delimits and encrypts each one under what stands here
// where it closes.

#include "preprocessor/protect_region_lines.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>

#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_key_block.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_pragma_line.h"

namespace delta {

ProtectDataDecryption DataDecryptionInEffect(const RegionKeyNames& names) {
  ProtectDataDecryption data;
  data.method = kDataMethod;
  data.keyname = ProtectPragmaValueBody(names.data_keyname);
  // §34.5.27 holds the blocks of one envelope to carrying the same data
  // decryption pragma expressions, and §34.5.10 and §34.5.13 define two of them
  // beside the name §34.5.12 does. They are taken here so that a region
  // changing one of them between two of its blocks is a region whose blocks can
  // be found to disagree, and the first two are taken to be written into the
  // blocks as well: §34.5.10.2 places the entity in a key_block wherever a
  // digital signature is used, and §34.5.12.2 places the name of the key there
  // wherever a digital envelope is used.
  data.keyowner = ProtectPragmaValueBody(names.data_keyowner);
  // §34.5.10.2 has the entity unchanged wherever it goes out, and the key block
  // of a signed region is one of the places it goes, so the spelling the source
  // used travels beside the body the name is read against.
  data.stated_keyowner = std::string(names.data_keyowner);
  data.public_key = names.data_public_key;
  return data;
}

namespace {

// The identifiers a line names for the algorithms a region's blocks are
// produced and opened with, each taken the way the names beside them are: the
// value standing where a region ends is the one that region's blocks belong to,
// and a line writing none of them leaves the earlier ones as they were.
void TakeMethodKeywords(std::string_view line, uint32_t line_num,
                        RegionKeyReader* reader) {
  // §34.5.11.2 has this identifier name "the encryption algorithm that shall be
  // used to encrypt subsequent begin-end blocks", so the value standing where a
  // region ends is the one that region was to be encrypted under. §34.5.11.1
  // spells the expression with a string, so a parenthesized pragma_value names
  // no algorithm and the identifier stated earlier stands.
  std::string_view data_method =
      KeywordSingleValueOnLine(line, kDataMethodKeyword);
  if (!data_method.empty()) {
    reader->data_method = data_method;
    reader->data_method_line = line_num;
  }
  // §34.5.21 puts the identifier in effect for the blocks written after it, so
  // the value standing where a region ends is the one that region's digests
  // belong to.
  std::string_view digest_method =
      KeywordValueOnLine(line, kDigestMethodKeyword);
  if (!digest_method.empty()) {
    reader->digest_method = digest_method;
    reader->digest_method_line = line_num;
  }
  // §34.5.17 names the cipher those digests are encrypted under, which is a
  // separate identifier from the one computing them: a digest is computed and
  // then put under a key, and neither step says anything about the other.
  std::string_view digest_key_method =
      KeywordValueOnLine(line, kDigestKeyMethodKeyword);
  if (!digest_key_method.empty()) reader->digest_key_method = digest_key_method;
  // §34.5.24 names the algorithm the region's own keys are encrypted under.
  // §34.5.24.1 spells the expression with a string, so a parenthesized
  // pragma_value names no algorithm and the identifier stated earlier stands:
  // an encrypting tool that took the list would write it onto the envelope,
  // where §22.11 admits no such expression and a reader would find the
  // identifier it needs to open the key blocks missing. The two method keywords
  // above are read without that question being asked, and #3277 covers them.
  std::string_view key_method =
      KeywordSingleValueOnLine(line, kKeyMethodKeyword);
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

// The documentation the region wrote for nothing to interpret, appended to
// whatever it wrote earlier rather than replacing it.
//
// §34.5.30.2 has the entire comment including the beginning pragma output in
// cleartext, so the directive is written back here rather than the value being
// stored for somebody else to spell. §34.5.30.1 writes the value as a string,
// which is one written thing, so a parenthesized list of further expressions is
// not the value this keyword is defined with: taking one would publish a list
// of somebody's subkeywords in the clear on the envelope, where a copyright
// notice belongs.
void TakeComment(std::string_view line, RegionKeyReader* reader) {
  std::string_view comment = KeywordSingleValueOnLine(line, kCommentKeyword);
  if (comment.empty()) return;
  reader->comment_directives.append(ProtectCommentDirective(comment));
}

// Everything the reading has gathered, put back to what it held before the
// reading began.
//
// §34.5.31.2 states this of an encrypting tool as well as of a tool that reads:
// following the reset, every protect pragma keyword stands at its default. What
// the reading gathers is those keywords' values -- the entities and the names
// designating their keys, the algorithms, the coding scheme and the blocks a
// text asked for -- so putting them back is dropping them. §34.5.31.1 writes
// the keyword standing alone, so a value written against it is not the
// expression that subclause defines and puts nothing back.
//
// The documentation gathered under §34.5.30.2 is not among them. That subclause
// asks for the comment found in a begin-end to be output ahead of that block's
// data, and a comment written before the reset was found there whatever the
// reset goes on to do to the keyword: what is held here is an output already
// owed rather than a value something later reads.
void TakeReset(std::string_view line, RegionKeyReader* reader) {
  if (!NamesBareKeyword(line, kResetKeyword)) return;
  std::string documented = std::move(reader->comment_directives);
  *reader = {};
  reader->comment_directives = std::move(documented);
}

// The names a line designates the region's keys by: the data key and the entity
// that provided it, the digest key and its own entity, and the key the region
// designates for keys of its own.
void TakeKeyDesignations(std::string_view line, uint32_t line_num,
                         RegionKeyReader* reader) {
  RegionKeyNames* names = &reader->names;
  // §34.5.12.1 writes the value as a string, and §34.5.12.2 has the name
  // written onto the envelope in the clear, where a list would go out quoted as
  // though it were the name picking one key of the region's entity out.
  std::string_view keyname =
      KeywordSingleValueOnLine(line, kDataKeynameKeyword);
  if (!keyname.empty()) names->data_keyname = keyname;
  // §34.5.10.1 writes the value as a string, so taking a parenthesized list
  // would write a list of somebody's subkeywords onto the envelope in the
  // clear, quoted as though it were the entity that provided the region's keys.
  std::string_view keyowner =
      KeywordSingleValueOnLine(line, kDataKeyownerKeyword);
  if (!keyowner.empty()) names->data_keyowner = keyowner;
  // §34.5.18.1 writes the value as a string, and §34.5.18.2 has the name
  // written onto the envelope in the clear, where a list would go out quoted as
  // though it were the name of the key a region's digest is under.
  std::string_view digest =
      KeywordSingleValueOnLine(line, kDigestKeynameKeyword);
  if (!digest.empty()) names->digest_keyname = digest;
  // §34.5.16 names the entity that provided the key the digest is under, which
  // the digest's own key name is read against rather than the data's entity.
  // §34.5.16.1 writes the value as a string, and §34.5.16.2 sends the name to a
  // digest_key_block the standard defines nowhere, so a list taken here is
  // published on the envelope in the clear as the entity.
  std::string_view provider =
      KeywordSingleValueOnLine(line, kDigestKeyownerKeyword);
  if (!provider.empty()) names->digest_keyowner = provider;
  // §34.5.25.1 and §34.5.23.1 write their values as strings as well, and
  // §34.5.25.2 and §34.5.23.2 have both written onto the envelope in the clear.
  // They are what a reader combines to reach the key opening a key block, so a
  // list taken here publishes a way in that no reader can follow.
  std::string_view key_name =
      KeywordSingleValueOnLine(line, kKeyKeynameKeyword);
  std::string_view key_owner =
      KeywordSingleValueOnLine(line, kKeyKeyownerKeyword);
  if (!key_owner.empty()) names->key_keyowner = key_owner;
  // §34.5.27 owes a key block to each key the text designates for the region's
  // own keys, so the designation is recorded as a request beside being kept as
  // the name in effect. The entity it is read against is the one standing here,
  // which is why the request is made once the line has been read whole rather
  // than where the name itself was taken.
  // A list designates nothing and so asks for no block, a text that designated
  // no key for its own keys having asked for nothing to carry one.
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
  // The reset is answered ahead of the keywords a line may write beside it,
  // because §34.4 reads a directive's expressions left to right and a text
  // putting the keywords back before stating new ones is the order an author
  // writes: what follows the reset on the line is stated after it.
  TakeReset(line, reader);
  TakeAuthorship(line, reader);
  TakeComment(line, reader);
  TakeKeyDesignations(line, line_num, reader);
  TakeMethodKeywords(line, line_num, reader);
  TakeAnnouncements(line, reader);
}

}  // namespace

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

}  // namespace delta
