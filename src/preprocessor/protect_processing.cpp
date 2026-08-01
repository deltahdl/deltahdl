#include "preprocessor/protect_processing.h"

#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_key_block.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_pragma_line.h"

namespace delta {
namespace {

// The expression that closes the decryption envelope an encryption envelope is
// transformed into. The other three delimiting words this file reads -- the
// pair delimiting the encryption envelope, and the one opening the decryption
// envelope -- are spelled beside the subclauses defining them, in
// protect_envelope.h, so the word this file takes as the start or end of a
// region is the word the envelope state takes for the same thing.
constexpr std::string_view kEndDecryptionKeyword = "end_protected";

// How a region's cleartext becomes the bytes a block records, and those bytes
// the cleartext again, is written in protect_processing_cipher.cpp. What one
// line of a source text says -- which protect pragma keywords it names, and how
// -- is answered in protect_pragma_line.cpp. What the envelope taking a
// region's place says is written in protect_envelope_output.cpp. What this file
// does is read a source text for the regions it delimits and settle which key
// each of them is written under; the other three are reached through the
// declarations they share.

// How many previously generated begin_protected-end_protected blocks the
// reading stands inside.
//
// §34.5.3 has the contents of such a block treated as input cleartext: the
// protect pragma expressions written in it are not interpreted and do not
// override the values the current encryption has in effect. The reading
// therefore has to know it is inside one before it reads a line rather than
// after, so a whole source text is walked through one of these.
//
// The two delimiting expressions are inside as well. What they describe is the
// envelope some earlier encryption produced, and letting that description into
// the reading is exactly the corruption of the current encryption's values
// §34.5.3 rules out, so the block runs from the line opening it through the
// line closing it.
//
// §34.5.1 allows further such blocks inside one, treating them as bytes of it
// like everything else, so what ends a block is the closing expression
// matching its own opening one rather than the first one encountered. A
// closing expression with nothing open closes nothing and is a line of the
// text like any other.
class PreviouslyProtectedBlock {
 public:
  // Applies one line, and returns whether that line belongs to a previously
  // generated protected block.
  //
  // §34.5.3.1 defines the word opening such a block as the pragma_keyword
  // standing alone, so a line is only opening one where it named that word in
  // that spelling. A line writing a pragma_value against the word opens
  // nothing and is text of whatever region encloses it, which is what keeps
  // this walk from taking an arbitrary run of an author's design for somebody
  // else's already-protected model.
  bool Contains(std::string_view line) {
    if (NamesBareKeyword(line, kBeginDecryptionKeyword)) {
      ++depth_;
      return true;
    }
    if (depth_ > 0 && NamesBareKeyword(line, kEndDecryptionKeyword)) {
      --depth_;
      return true;
    }
    return depth_ > 0;
  }

 private:
  size_t depth_ = 0;
};

// Which of the two encryption envelope delimiters a directive line carries.
enum class EnvelopeDelimiter : uint8_t { kNone, kBegin, kEnd };

// A delimiter found on a directive line, together with the word that spelled
// it. The word is kept as a view into the line so the rest of the line can be
// told apart from it: the expressions written beside a delimiter specify the
// envelope it opens or closes, and they are carried into the envelope that
// takes its place rather than being read as part of the delimiter.
struct DelimiterMatch {
  EnvelopeDelimiter kind;
  std::string_view keyword;
};

// A line whose delimiting word was written with a pragma_value against it is a
// line that delimits nothing: §34.5.1.1 defines the opening word standing
// alone and §34.5.2.1 defines the closing word the same way, so the walk
// carries on past either one and, finding no delimiter, leaves the line among
// the text this transformation copies rather than reads.
//
// A closing word written that way leaves the region it was meant to close
// still open, so the reading runs on to whatever closes next -- or to the end
// of the text, where a region that was never closed goes back as it was
// written. Reading such a word as the end of the region anyway would seal it
// at a point the standard does not put an end there.
DelimiterMatch DelimiterOfLine(std::string_view line) {
  std::string_view body;
  if (!ProtectPragmaLine(line, &body)) return {EnvelopeDelimiter::kNone, {}};
  for (const ListedKeyword& keyword : TopLevelKeywords(body)) {
    if (OpensEncryptionEnvelope(keyword.name, keyword.has_value)) {
      return {EnvelopeDelimiter::kBegin, keyword.name};
    }
    if (ClosesEncryptionEnvelope(keyword.name, keyword.has_value)) {
      return {EnvelopeDelimiter::kEnd, keyword.name};
    }
  }
  return {EnvelopeDelimiter::kNone, {}};
}

// The expressions a delimiter is followed by on its own line: `rest` up to any
// comment written there, and without the whitespace that ran up to it.
//
// Neither a comment nor the space ahead of it is a pragma expression, and
// neither states anything about the envelope, so neither is among the things
// this transformation carries. Leaving the comment behind is also what keeps
// the envelope readable: a block comment the author never closed would
// otherwise be carried onto the produced directive and take the expressions
// written after it -- the description of the encryption, and the block itself
// -- into the comment with it.
std::string_view ExpressionsAfterDelimiter(std::string_view rest) {
  size_t end = rest.size();
  size_t i = 0;
  while (i < rest.size()) {
    // A comment opener inside a string value is content of that value.
    if (rest[i] == '"') {
      i = SkipStringValue(rest, i);
    } else if (StartsLineComment(rest, i) || rest.compare(i, 2, "/*") == 0) {
      end = i;
      break;
    } else {
      ++i;
    }
  }
  return TrimTrailing(rest.substr(0, end));
}

// The directive that delimits a decryption envelope where `line` delimited an
// encryption one.
//
// Only the word naming the delimiter is transformed, because only that word
// said which of the two modes the envelope was defined for. Every expression
// beside it -- who wrote the design, which algorithm and key name were asked
// for, what a run of it is licensed on -- specified the encryption envelope,
// and each is written out again exactly as it stands so that it goes on
// specifying the envelope standing in its place. The line's own leading
// whitespace and directive text are kept for the same reason.
//
// An expression written ahead of the delimiter describes the envelope and an
// expression written after it describes the enclosed region, so carrying each
// one across on the side it was written on is what keeps the two apart.
std::string TransformedDelimiterLine(std::string_view line,
                                     const DelimiterMatch& delimiter,
                                     std::string_view replacement) {
  size_t at = static_cast<size_t>(delimiter.keyword.data() - line.data());
  std::string transformed(line.substr(0, at));
  transformed.append(replacement);
  transformed.append(
      ExpressionsAfterDelimiter(line.substr(at + delimiter.keyword.size())));
  // The last line of a source text need not be terminated, and a trimmed
  // comment takes the terminator with it. What follows this line either way is
  // a directive of its own.
  if (transformed.back() != '\n') transformed.push_back('\n');
  return transformed;
}

// Splits `text` at every newline, keeping each terminator with the line it
// ends, so putting the pieces back together reproduces `text` byte for byte.
std::vector<std::string_view> SplitLines(std::string_view text) {
  std::vector<std::string_view> lines;
  size_t pos = 0;
  while (pos < text.size()) {
    size_t eol = text.find('\n', pos);
    size_t end = eol == std::string_view::npos ? text.size() : eol + 1;
    lines.push_back(text.substr(pos, end - pos));
    pos = end;
  }
  return lines;
}

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
void TakeKeyPublicKeyLine(std::string_view line, RegionKeyReader* reader) {
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
  reader->key_blocks.DesignatePublicKey(reader->names.key_keyowner,
                                        reader->names.key_public_key,
                                        DataDecryptionInEffect(reader->names));
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

void TakeKeyNames(std::string_view line, RegionKeyReader* reader) {
  if (reader->encoded_key_next) {
    TakeKeyPublicKeyLine(line, reader);
    return;
  }
  if (reader->encoded_data_key_next) {
    TakeDataPublicKeyLine(line, reader);
    return;
  }
  if (reader->encoded_digest_key_next) {
    TakeDigestPublicKeyLine(line, reader);
    return;
  }
  RegionKeyNames* names = &reader->names;
  // §34.5.5 names whoever wrote the design. It is taken the way the names below
  // are: the value standing where a region ends is the one that region's
  // envelope carries, and a line writing none leaves the earlier one as it was.
  std::string_view author = KeywordValueOnLine(line, kAuthorKeyword);
  if (!author.empty()) reader->author = author;
  // §34.5.9 puts the scheme in effect wherever the expression naming it was
  // written, so a text may state one scheme for one region and another for the
  // next, and the reading takes each as it passes.
  std::string_view encoding = KeywordValueOnLine(line, kEncodingKeyword);
  if (!encoding.empty()) reader->encoding = ParseProtectEncoding(encoding);
  std::string_view keyname = KeywordValueOnLine(line, kDataKeynameKeyword);
  if (!keyname.empty()) names->data_keyname = keyname;
  std::string_view keyowner = KeywordValueOnLine(line, kDataKeyownerKeyword);
  if (!keyowner.empty()) names->data_keyowner = keyowner;
  std::string_view digest = KeywordValueOnLine(line, kDigestKeynameKeyword);
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
                                 DataDecryptionInEffect(*names));
  }
  TakeMethodKeywords(line, reader);
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

// The same, for a line whose place in the input has already been settled.
// `contained` says a previously generated protected block holds the line, and
// §34.5.3 leaves the expressions of such a line uninterpreted: they describe
// an envelope some earlier encryption produced, so none of them is allowed to
// displace what the encryption now in process has in effect.
void TakeKeyNamesOutsideProtectedBlock(std::string_view line, bool contained,
                                       RegionKeyReader* reader) {
  if (!contained) TakeKeyNames(line, reader);
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
  // of it, the expression naming the author being written in the clear inside
  // the envelope instead, so a directive carrying one is held back from here.
  std::string body;
  RegionKeyReader written_inside;
};

// Whether one line of an encryption envelope's enclosed text carries the
// expression that names the design's author.
//
// It is the spelling §34.5.5.1 defines that counts: the keyword with a value
// written against it. The keyword standing alone names nobody, so §34.5.5 says
// nothing about it and §34.5.1's rule for everything else between the
// delimiters is what governs -- it goes into the block along with the rest.
//
// A line a previously generated protected block contains carries nothing of the
// kind either. §34.5.3 leaves the expressions of such a line uninterpreted and
// §34.5.1 has that block travel into the larger envelope as the bytes it is
// written with, so a name written there belongs to a design some earlier
// encryption sealed rather than to this one.
bool CarriesAuthorExpression(std::string_view line, bool previously_protected) {
  return !previously_protected &&
         !KeywordValueOnLine(line, kAuthorKeyword).empty();
}

// Adds one line of enclosed text to the region being read: to the text that
// goes back where the region cannot be encrypted, to the text a block records
// unless §34.5.5 holds it back from there, and to what the region has said
// about itself.
void AppendEnvelopeLine(std::string_view line, bool previously_protected,
                        ReadRegion* region) {
  region->source_body.append(line);
  if (!CarriesAuthorExpression(line, previously_protected)) {
    region->body.append(line);
  }
  // What the region itself wrote is kept apart from what is merely in effect
  // over it: those are the expressions the envelope has to carry in the clear,
  // the rest of the region's text being about to stop being readable. One
  // written outside the region is in the output already.
  TakeKeyNamesOutsideProtectedBlock(line, previously_protected,
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
ProtectKeyBlockRequests DesignatedKeyBlocks(const RegionKeyNames& names) {
  ProtectKeyBlockRequests requests;
  if (!names.key_keyname.empty()) {
    requests.Designate(names.key_keyowner, names.key_keyname,
                       DataDecryptionInEffect(names));
  } else if (!names.key_public_key.empty()) {
    requests.DesignatePublicKey(names.key_keyowner, names.key_public_key,
                                DataDecryptionInEffect(names));
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
                                     const ProtectKeyList& keys) {
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
  ProtectKeyBlockRequests requests = region.written_inside.key_blocks.Empty()
                                         ? DesignatedKeyBlocks(in_effect.names)
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

// One line of the input, read for the two things an encrypting tool has to
// know about it before it does anything else with it: whether a previously
// generated protected block contains it, and which delimiter of an encryption
// envelope it carries.
//
// The two go together because the first decides the second. §34.5.3 leaves the
// protect pragmas inside such a block uninterpreted, and a word that opens or
// closes a region is a protect pragma like any other, so a line inside a block
// delimits nothing however it is spelled.
struct InputLine {
  bool previously_protected;
  DelimiterMatch delimiter;
};

// §34.5.1 makes a region opened inside a region that is still open an error.
// The opening expression marks the point encryption begins at, and a text that
// marks a second such point before marking where the first region ends has
// asked for one block of cleartext inside another.
//
// The line is still read as the text it is: the transformation runs to the end
// of the input either way, and §34.5.1 has everything standing between an
// opening expression and the closing one that answers it -- other protect
// pragmas included -- encrypted into the enclosing region's block. What the
// condition costs is the report rather than the transformation, which is how
// every other condition an encrypting tool's input can carry is treated here.
//
// It is a delimiter of this reading's own that counts. A line a previously
// generated protected block contains delimits nothing, because §34.5.3 leaves
// its expressions uninterpreted, so an already-protected model sealed inside a
// region is the arrangement §34.5.1 permits rather than the one it rules out.
// So is an opening word written with a pragma_value against it, which §34.5.1.1
// leaves naming no opening expression at all.
void ReportNestedRegion(const DelimiterMatch& delimiter,
                        ProtectEncryptionReport* report) {
  if (report != nullptr && delimiter.kind == EnvelopeDelimiter::kBegin) {
    report->nested_begin_block = true;
  }
}

InputLine ReadInputLine(std::string_view line, PreviouslyProtectedBlock* block,
                        ProtectEncryptionReport* report) {
  if (block->Contains(line)) {
    return {true, {EnvelopeDelimiter::kNone, {}}};
  }
  // §34.5.15 makes a data block found in an input file an error unless a
  // previously generated protected block contains it. This line is outside
  // every one of them, so a block written here is the block of no envelope --
  // there is nothing for it to have come out of, and nothing that could read
  // it back. The line is still carried across like any other; what the
  // condition costs is a report rather than the transformation.
  if (report != nullptr && NamesKeyword(line, kDataBlockKeyword)) {
    report->data_block_outside_protected_block = true;
  }
  // §34.5.27 states the same of a key block, and it costs the same: outside
  // every previously generated protected block there is no envelope whose keys
  // a key block here could be carrying, and no key it could have been encrypted
  // under either.
  if (report != nullptr && NamesKeyword(line, kKeyBlockKeyword)) {
    report->key_block_outside_protected_block = true;
  }
  return {false, DelimiterOfLine(line)};
}

}  // namespace

std::string EncryptEnvelopes(std::string_view source_text,
                             std::string_view exchange_key,
                             const ProtectKeyList& keys,
                             ProtectEncryptionReport* report) {
  // With neither a key of one's own nor keys supplied under the names that
  // select them, there is nothing any region could be encrypted under, so the
  // text stands as it is written.
  //
  // What a caller asking for a report is still owed is the reading. §34.5.1
  // makes a region opened inside an open one an error in the text itself, and a
  // text carries that error whether or not a key was supplied to act on it, so
  // a caller that asked to be told is told rather than handed its text back in
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
  if (report == nullptr && exchange_key.empty() && keys.Empty()) {
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
  for (std::string_view line : SplitLines(source_text)) {
    InputLine input = ReadInputLine(line, &previously_protected, report);
    TakeKeyNamesOutsideProtectedBlock(line, input.previously_protected,
                                      &in_effect);
    DelimiterMatch delimiter = input.delimiter;
    // §34.5.2.2 has the closing expression state, in the input cleartext, where
    // the region that is to be encrypted stops. The region therefore ends at
    // the line the word is written on rather than at the end of the text or at
    // some later delimiter, so this is where the lines gathered so far become a
    // block and the lines after it go back to being carried across.
    if (in_envelope && delimiter.kind == EnvelopeDelimiter::kEnd) {
      RegionEncryption how =
          RegionEncryptionFor(in_effect, region, exchange_key, keys);
      // §34.5.27 has every key block of one envelope encode the same data
      // decryption key data, so a region whose data decryption pragma
      // expressions changed value between two of them is reported rather than
      // left carrying blocks that open onto different accounts of one key.
      if (report != nullptr && how.key_blocks.data_changed) {
        report->key_block_data_changed = true;
      }
      transformed.append(
          ClosedRegionText(region, in_effect, line, delimiter, how));
      in_envelope = false;
    } else if (in_envelope) {
      // §34.5.1 rules out a second opening expression here, this region not
      // having been closed yet, so a line carrying one is reported before it is
      // taken as text of the region.
      ReportNestedRegion(delimiter, report);
      // §34.5.3 and §34.5.4 have the two expressions delimiting a previously
      // generated block, and everything between them, encrypted into the block
      // of the envelope enclosing them. Adding the line unread is what does
      // that: an already-protected model travels into the larger one as the
      // bytes it is written with.
      AppendEnvelopeLine(line, input.previously_protected, &region);
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
