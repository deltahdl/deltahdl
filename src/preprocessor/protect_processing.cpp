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
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_key_block.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_keywords.h"

namespace delta {
namespace {

// The two expressions that delimit the decryption envelope an encryption
// envelope is transformed into. The pair delimiting the encryption envelope
// read here is spelled beside the subclauses defining those two words, in
// protect_envelope.h, so the word this file takes as the end of a region is
// the word the envelope state takes for the same thing.
constexpr std::string_view kBeginDecryptionKeyword = "begin_protected";
constexpr std::string_view kEndDecryptionKeyword = "end_protected";

// How a region's cleartext becomes the bytes a block records, and those bytes
// the cleartext again, is written in protect_processing_cipher.cpp. What the
// envelope taking a region's place says is written in
// protect_envelope_output.cpp. What this file does is read a source text for
// the regions it delimits and settle which key each of them is written under;
// the other two halves are reached through the declarations they share.

bool IsIdentifierChar(char c) {
  return std::isalnum(static_cast<unsigned char>(c)) != 0 || c == '_' ||
         c == '$';
}

bool IsIdentifierStart(char c) {
  return std::isalpha(static_cast<unsigned char>(c)) != 0 || c == '_';
}

std::string_view TrimLeading(std::string_view text) {
  size_t i = 0;
  while (i < text.size() && std::isspace(static_cast<unsigned char>(text[i]))) {
    ++i;
  }
  return text.substr(i);
}

// Consumes `word` from the front of `text` when it stands there as a whole
// word. A longer name that merely starts with the same letters is a different
// name, so it is left alone.
bool ConsumeWord(std::string_view& text, std::string_view word) {
  if (text.substr(0, word.size()) != word) return false;
  std::string_view rest = text.substr(word.size());
  if (!rest.empty() && IsIdentifierChar(rest.front())) return false;
  text = rest;
  return true;
}

// True when `line` is a directive naming the pragma that describes protected
// envelopes, with `*body` left holding the expression list written after the
// name. These are the only lines envelope encryption reads; every other line
// it copies without asking what it says.
bool ProtectPragmaLine(std::string_view line, std::string_view* body) {
  std::string_view rest = TrimLeading(line);
  if (rest.empty() || rest.front() != '`') return false;
  rest.remove_prefix(1);
  if (!ConsumeWord(rest, "pragma")) return false;
  rest = TrimLeading(rest);
  if (!ConsumeWord(rest, kProtectPragmaName)) return false;
  *body = rest;
  return true;
}

// Advances past a parenthesized value, returning the index just after the
// parenthesis that closes the one opening at `i`.
size_t SkipParenGroup(std::string_view body, size_t i) {
  size_t depth = 0;
  while (i < body.size()) {
    if (body[i] == '(') ++depth;
    if (body[i] == ')' && --depth == 0) return i + 1;
    ++i;
  }
  return i;
}

// Advances past a string value, returning the index just after its closing
// quote. A quote written behind a backslash is content rather than the end.
size_t SkipStringValue(std::string_view body, size_t i) {
  ++i;
  while (i < body.size()) {
    if (body[i] == '\\' && i + 1 < body.size()) {
      i += 2;
      continue;
    }
    if (body[i] == '"') return i + 1;
    ++i;
  }
  return i;
}

bool StartsLineComment(std::string_view body, size_t i) {
  return body.compare(i, 2, "//") == 0;
}

// One keyword a directive's expression list names, and whether a pragma_value
// was written against it. §22.5.1 spells a pragma expression either way, and a
// keyword whose own definition admits one of the two spellings is read against
// this, so the walk that finds a name also records how the name was written.
//
// `value` is the text of that pragma_value as the directive wrote it, quotes
// and all, and is empty where the keyword stood alone. A keyword whose
// definition turns on what its value says -- rather than only on whether one
// was written -- is read against this.
struct ListedKeyword {
  std::string_view name;
  bool has_value;
  std::string_view value;
};

// Where the pragma_value being read starts, once an '=' has opened one. A list
// is walked from left to right, so at most one value is open at any point and
// the name it belongs to is the one collected last.
struct OpenValue {
  bool open;
  size_t start;
};

std::string_view TrimTrailing(std::string_view text) {
  size_t end = text.size();
  while (end > 0 && std::isspace(static_cast<unsigned char>(text[end - 1]))) {
    --end;
  }
  return text.substr(0, end);
}

// Ends the value that has stood open since its '=': what lies between there
// and `end` was written against the name collected last, without the
// whitespace separating it from the punctuation on either side. A value with
// no name to its left belongs to no expression of the list and is dropped.
void CloseValue(std::string_view body, size_t end, OpenValue* value,
                std::vector<ListedKeyword>* keywords) {
  if (!value->open) return;
  value->open = false;
  if (keywords->empty()) return;
  keywords->back().value =
      TrimTrailing(TrimLeading(body.substr(value->start, end - value->start)));
}

// Scans the identifier starting at `i`, collecting it when it names an
// expression of the list rather than qualifying a value, and returns the index
// just past it.
size_t ScanKeyword(std::string_view body, size_t i, bool in_value,
                   std::vector<ListedKeyword>* keywords) {
  size_t start = i;
  while (i < body.size() && IsIdentifierChar(body[i])) ++i;
  if (!in_value) keywords->push_back({body.substr(start, i - start), false});
  return i;
}

// Records that a pragma_value was written against the name collected last,
// which is the name an '=' reached at this level belongs to. A directive that
// opens with an '=' has collected nothing yet, and an expression with no
// keyword to the left of its '=' is not one of these.
void MarkLastKeywordValued(std::vector<ListedKeyword>* keywords) {
  if (!keywords->empty()) keywords->back().has_value = true;
}

// The keywords a directive's expression list names at its own level, in
// writing order. A word inside a parenthesized value, one inside a string, and
// one standing on the right of an '=' all qualify a value rather than naming
// an expression of the list, so none of them is collected. A one-line comment
// is not part of the list at all and ends the walk.
//
// A value written in parentheses or in quotes is stepped over whole, so
// neither the '=' inside one nor the words it separates reach this level at
// all, and each '=' that does reach it belongs to a name of the list.
std::vector<ListedKeyword> TopLevelKeywords(std::string_view body) {
  std::vector<ListedKeyword> keywords;
  size_t i = 0;
  bool in_value = false;
  OpenValue value{false, 0};
  while (i < body.size()) {
    char c = body[i];
    if (StartsLineComment(body, i)) {
      break;
    } else if (c == '(') {
      i = SkipParenGroup(body, i);
    } else if (c == '"') {
      i = SkipStringValue(body, i);
    } else if (c == ',') {
      CloseValue(body, i, &value, &keywords);
      in_value = false;
      ++i;
    } else if (c == '=') {
      in_value = true;
      MarkLastKeywordValued(&keywords);
      value = {true, i + 1};
      ++i;
    } else if (IsIdentifierStart(c)) {
      i = ScanKeyword(body, i, in_value, &keywords);
    } else {
      ++i;
    }
  }
  // A value runs to the comma that ends its expression, or, for the last
  // expression of the list, to the end of the list -- which a comment written
  // after it brings forward to where the comment starts.
  CloseValue(body, i, &value, &keywords);
  return keywords;
}

// The pragma_value a protect pragma directive line writes against `keyword` on
// its own expression list, and an empty view where the line is not such a
// directive, does not name that keyword at its own level, or names it with no
// value written against it.
std::string_view KeywordValueOnLine(std::string_view line,
                                    std::string_view keyword) {
  std::string_view body;
  if (!ProtectPragmaLine(line, &body)) return {};
  for (const ListedKeyword& listed : TopLevelKeywords(body)) {
    if (listed.name == keyword && listed.has_value) return listed.value;
  }
  return {};
}

// True when a protect pragma directive line names `keyword` on its own
// expression list with nothing written against it.
//
// A keyword whose definition writes it standing alone is read against this
// rather than against a value: §34.5.26.1 defines its keyword that way, what
// the keyword designates being written on the line beneath rather than on the
// line itself, so a line is only announcing that designation when it named the
// keyword in the spelling the keyword is defined in.
bool NamesBareKeyword(std::string_view line, std::string_view keyword) {
  std::string_view body;
  if (!ProtectPragmaLine(line, &body)) return false;
  for (const ListedKeyword& listed : TopLevelKeywords(body)) {
    if (listed.name == keyword && !listed.has_value) return true;
  }
  return false;
}

// True when a protect pragma directive line names `keyword` on its own
// expression list, in either of the two spellings §22.5.1 gives a pragma
// expression.
//
// A rule about a keyword being written at all rather than about what it
// carries is read against this. §34.5.15 states one: a data block found in an
// input file is an error wherever no previously generated protected block
// encloses it, and it is the naming of the keyword that puts a block there,
// whether the block is written on the line after it or as the value against
// it.
bool NamesKeyword(std::string_view line, std::string_view keyword) {
  std::string_view body;
  if (!ProtectPragmaLine(line, &body)) return false;
  for (const ListedKeyword& listed : TopLevelKeywords(body)) {
    if (listed.name == keyword) return true;
  }
  return false;
}

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

// A line whose opening word was written with a pragma_value against it is a
// line that opens nothing: §34.5.1.1 defines that word standing alone, so the
// walk carries on past it and, finding no delimiter, leaves the line among the
// text this transformation copies rather than reads.
DelimiterMatch DelimiterOfLine(std::string_view line) {
  std::string_view body;
  if (!ProtectPragmaLine(line, &body)) return {EnvelopeDelimiter::kNone, {}};
  for (const ListedKeyword& keyword : TopLevelKeywords(body)) {
    if (OpensEncryptionEnvelope(keyword.name, keyword.has_value)) {
      return {EnvelopeDelimiter::kBegin, keyword.name};
    }
    if (keyword.name == kEndEncryptionKeyword) {
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
  // The identifier the text named the algorithm its digests are computed with,
  // empty where the text named none. It is carried beside the names for the
  // reason they are carried at all: §34.5.21 has the identifier unchanged in
  // what an encrypting tool writes out, so it belongs to the description of the
  // envelope rather than to the lines about to stop being readable.
  std::string_view digest_method;
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

void TakeKeyNames(std::string_view line, RegionKeyReader* reader) {
  if (reader->encoded_key_next) {
    TakeKeyPublicKeyLine(line, reader);
    return;
  }
  RegionKeyNames* names = &reader->names;
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
  // §34.5.21 puts the identifier in effect for the blocks written after it, so
  // the value standing where a region ends is the one that region's digests
  // belong to, and a line writing none leaves the earlier one as it was.
  std::string_view digest_method =
      KeywordValueOnLine(line, kDigestMethodKeyword);
  if (!digest_method.empty()) reader->digest_method = digest_method;
  // §34.5.24 names the algorithm the region's own keys are encrypted under, and
  // the reading takes it the same way: the value standing where a region ends
  // is the one that region's keys belong to.
  std::string_view key_method = KeywordValueOnLine(line, kKeyMethodKeyword);
  if (!key_method.empty()) reader->key_method = key_method;
  reader->encoded_key_next = NamesBareKeyword(line, kKeyPublicKeyKeyword);
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
  std::string body;
  RegionKeyReader written_inside;
};

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
std::string_view RegionKey(const RegionKeyNames& names,
                           std::string_view exchange_key,
                           const ProtectKeyList& keys) {
  if (keys.Empty()) return exchange_key;
  return keys.KeyFor(ProtectPragmaValueBody(names.data_keyowner),
                     ProtectPragmaValueBody(names.data_keyname));
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
RegionEncryption RegionEncryptionFor(const RegionKeyReader& in_effect,
                                     const ReadRegion& region,
                                     std::string_view exchange_key,
                                     const ProtectKeyList& keys) {
  RegionEncryption how;
  std::string_view named = RegionKey(in_effect.names, exchange_key, keys);
  if (!named.empty()) {
    how.key = named;
    return how;
  }
  ProtectKeyBlockRequests requests = region.written_inside.key_blocks.Empty()
                                         ? DesignatedKeyBlocks(in_effect.names)
                                         : region.written_inside.key_blocks;
  how.key_blocks = ProtectKeyBlocksFor(
      requests, region.body, keys,
      EnvelopeBlockEncoding(region.written_inside.encoding));
  how.key = how.key_blocks.data_key;
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
std::string ClosedRegionText(const ReadRegion& region, std::string_view line,
                             const DelimiterMatch& delimiter,
                             const RegionEncryption& how) {
  if (how.key.empty()) {
    std::string text(region.opening_line);
    text.append(region.body).append(line);
    return text;
  }
  std::string closing_directive =
      TransformedDelimiterLine(line, delimiter, kEndDecryptionKeyword);
  EncryptionEnvelope envelope;
  envelope.begin_directive = region.opening_directive;
  envelope.body = region.body;
  envelope.end_directive = closing_directive;
  envelope.names = region.written_inside.names;
  envelope.digest_method = region.written_inside.digest_method;
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
  if (exchange_key.empty() && keys.Empty()) return std::string(source_text);
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
      transformed.append(ClosedRegionText(region, line, delimiter, how));
      in_envelope = false;
    } else if (in_envelope) {
      // §34.5.3 and §34.5.4 have the two expressions delimiting a previously
      // generated block, and everything between them, encrypted into the block
      // of the envelope enclosing them. Appending the line unread is what does
      // that: an already-protected model travels into the larger one as the
      // bytes it is written with.
      region.body.append(line);
      // What the region itself wrote is kept apart from what is merely in
      // effect over it: those are the names the envelope has to carry in the
      // clear, the rest of the region's text being about to stop being
      // readable. A name written outside the region is in the output already.
      TakeKeyNamesOutsideProtectedBlock(line, input.previously_protected,
                                        &region.written_inside);
    } else if (delimiter.kind == EnvelopeDelimiter::kBegin) {
      in_envelope = true;
      region.opening_line = line;
      region.opening_directive =
          TransformedDelimiterLine(line, delimiter, kBeginDecryptionKeyword);
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
    transformed.append(region.body);
  }
  return transformed;
}

}  // namespace delta
