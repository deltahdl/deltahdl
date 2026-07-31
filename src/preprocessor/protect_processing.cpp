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

// An encrypted region records a fingerprint of its own text ahead of the text
// itself. Recovering that fingerprint is how the decrypting half tells the key
// the region was encrypted under from any other key it might be given: a
// different key yields different bytes throughout, and the fingerprint they
// carry no longer describes the text beside it.
constexpr size_t kFingerprintBytes = 4;
constexpr uint32_t kFingerprintBasis = 0x811C9DC5U;
constexpr uint32_t kFingerprintFactor = 0x01000193U;

uint32_t FingerprintOf(std::string_view text) {
  uint32_t fingerprint = kFingerprintBasis;
  for (char c : text) {
    fingerprint ^= static_cast<uint8_t>(c);
    fingerprint *= kFingerprintFactor;
  }
  return fingerprint;
}

std::string FingerprintPrefix(uint32_t fingerprint) {
  std::string prefix;
  for (size_t n = kFingerprintBytes; n > 0; --n) {
    prefix.push_back(static_cast<char>((fingerprint >> ((n - 1) * 8)) & 0xFFU));
  }
  return prefix;
}

uint32_t ReadFingerprintPrefix(std::string_view bytes) {
  uint32_t fingerprint = 0;
  for (size_t n = 0; n < kFingerprintBytes; ++n) {
    auto byte = static_cast<uint8_t>(bytes[n]);
    fingerprint = (fingerprint << 8) | byte;
  }
  return fingerprint;
}

// The keyed step of both halves. Combining the bytes with the key twice gives
// the bytes back, which is what makes one key both encrypt and decrypt a
// region.
std::string CombineWithKey(std::string_view bytes, std::string_view key) {
  std::string combined;
  combined.reserve(bytes.size());
  for (size_t n = 0; n < bytes.size(); ++n) {
    auto byte = static_cast<uint8_t>(bytes[n]);
    auto key_byte = static_cast<uint8_t>(key[n % key.size()]);
    combined.push_back(static_cast<char>(byte ^ key_byte));
  }
  return combined;
}

// The block a region is recorded in is written as text by §34.5.9's coding
// schemes, which are spelled out in protect_encoding.h. Which scheme is used
// is what a text's encoding pragma expression settles, so the writing and the
// reading of a block are given a scheme rather than holding one of their own.

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

// How this implementation's own encryption is named to whatever reads an
// envelope it produced. The standard reserves identifiers for the ciphers it
// specifies and this is not one of those, so the name is spelled as this
// implementation's own rather than claiming a reserved one. The coding scheme
// the blocks are written in is named the same way, in protect_encoding.h.
constexpr std::string_view kEncryptAgent = "deltahdl";
constexpr std::string_view kDataMethod = "x-deltahdl-stream";

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
  // The coding scheme in effect where the reading stands, which §34.5.9 has
  // every encoded value of the text written under and §34.5.26 sends the
  // reader of a public key's line to. It is carried with the names because it
  // decides what one of them says: the same line of characters is one key
  // under one scheme and another key, or nothing at all, under another.
  ProtectEncoding encoding = DefaultProtectEncoding();
  bool encoded_key_next = false;
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
  // The coding scheme the enclosed text asked its blocks to be written under.
  // §34.5.9 has an encoding pragma expression found in the input specify how
  // the output is encoded, so what a region wrote for itself is what its own
  // blocks are written in, rather than the tool's choice standing over it.
  ProtectEncoding requested_encoding;
};

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
  if (!key_name.empty()) names->key_keyname = key_name;
  std::string_view key_owner = KeywordValueOnLine(line, kKeyKeyownerKeyword);
  if (!key_owner.empty()) names->key_keyowner = key_owner;
  // §34.5.21 puts the identifier in effect for the blocks written after it, so
  // the value standing where a region ends is the one that region's digests
  // belong to, and a line writing none leaves the earlier one as it was.
  std::string_view digest_method =
      KeywordValueOnLine(line, kDigestMethodKeyword);
  if (!digest_method.empty()) reader->digest_method = digest_method;
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

// The scheme the blocks of one envelope are written under: the one the
// enclosed text asked for, where a block of that scheme can be carried on the
// expression a block is written on, and this implementation's own otherwise.
//
// A line length the text stated is not carried across. It is a maximum on the
// characters of a line of the block, and a block written as the value of a
// pragma expression is written on the directive's own line, so a break put in
// to honor the maximum would end the directive rather than the line.
ProtectEncoding EnvelopeBlockEncoding(const ProtectEncoding& requested) {
  ProtectEncoding encoding = DefaultProtectEncoding();
  if (ProtectEncodingFitsPragmaValue(requested.enctype)) {
    encoding.enctype = requested.enctype;
  }
  return encoding;
}

// The encoding pragma expression written ahead of one block of an envelope:
// the scheme the block is written under, and the size of the data those
// characters stand for.
//
// §34.5.9 has a count added by the encrypting tool for each block it writes,
// and lets an expression be written ahead of each block rather than once for
// the envelope, which is what a text stating a count per block needs. A count
// belongs to one block, so an envelope carrying two blocks writes two of
// these.
std::string BlockEncodingDirective(const ProtectEncoding& encoding,
                                   size_t bytes) {
  ProtectEncoding described = encoding;
  described.bytes = bytes;
  described.has_bytes = true;
  return ProtectEncodingDirective(described);
}

// §34.5.26 has the public key written into every protected block it was used
// for, followed by its encoded value, and §34.5.9 has that value encoded in
// the scheme the envelope declares. A key the source wrote under some other
// scheme is therefore written back out under this envelope's: the value
// carried across is the key, and the characters standing for it are whichever
// the reader of this envelope will be reading.
void AppendKeyPublicKey(std::string_view key, const ProtectEncoding& encoding,
                        std::string* text) {
  text->append(BlockEncodingDirective(encoding, key.size()));
  text->append(ProtectKeyPublicKeyDirective(EncodeProtectBlock(key, encoding)));
}

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
                                   std::string_view region_key) {
  std::string text;
  text.append(envelope.begin_directive);
  // The scheme the envelope's blocks are written under is stated for the
  // envelope as a whole, ahead of everything depending on it, and each block
  // restates it with the count of what that block holds.
  ProtectEncoding block_encoding =
      EnvelopeBlockEncoding(envelope.requested_encoding);
  std::string envelope_encoding = ProtectEncodingValue(block_encoding);
  text.append(ProtectEnvelopeDescriptionDirectives(
      {kEncryptAgent, kDataMethod, envelope_encoding}));
  // §34.5.10 has the entity whose keys the data are under unchanged in what
  // the tool writes out, and §34.5.12 has the name of the key itself written
  // as cleartext. Either name the enclosed text stated would otherwise go into
  // the block along with the rest of that text, and a reader would have to
  // open the block to learn what opens it. Lifting them out is what the
  // standard's exceptions for these two keywords are for; the exception the
  // standard makes to the exception is the digital envelope mechanism, which
  // this implementation does not offer, so both are always written in the
  // clear. The entity comes first, the key name being read against it.
  if (!envelope.names.data_keyowner.empty()) {
    text.append(ProtectDataKeyownerDirective(envelope.names.data_keyowner));
  }
  if (!envelope.names.data_keyname.empty()) {
    text.append(ProtectDataKeynameDirective(envelope.names.data_keyname));
  }
  // §34.5.18 makes the same exception for the name of the key the region's
  // digest is under. A region that named a key for its digest named one the
  // data's key name does not stand for, so leaving it in the block would put
  // the one name a reader needs for the digest out of reach behind the data.
  if (!envelope.names.digest_keyname.empty()) {
    text.append(ProtectDigestKeynameDirective(envelope.names.digest_keyname));
  }
  // §34.5.21 makes the same exception for the identifier naming the algorithm
  // the region's digests are computed with, and it is written ahead of the
  // block rather than after it: what the identifier is needed for is
  // recomputing a digest of that block, so a reader has to have it in hand by
  // the time the block is reached.
  if (!envelope.digest_method.empty()) {
    text.append(ProtectDigestMethodDirective(envelope.digest_method));
  }
  // §34.5.23 has the entity whose keys a region's own keys are under unchanged
  // in what the tool writes out, and makes no exception at all: the exception
  // the other two entities have is a key block, and this is the entity whose
  // key opens that block. It comes ahead of the designations beneath it, each
  // of those being read against it.
  if (!envelope.names.key_keyowner.empty()) {
    text.append(ProtectKeyKeyownerDirective(envelope.names.key_keyowner));
  }
  // §34.5.25 has the name of the key a region's own keys are under written as
  // cleartext as well. It is the name a reader combines with the entity beside
  // it to reach the key the region is opened through, so leaving it among the
  // lines about to become unreadable would put the way in behind the door it
  // unlocks.
  if (!envelope.names.key_keyname.empty()) {
    text.append(ProtectKeyKeynameDirective(envelope.names.key_keyname));
  }
  // §34.5.26 has the other designation of that key written into every
  // protected block it was used for, with its encoded value beneath it. A
  // region that designated its key this way is opened through this value, so
  // an envelope that kept it inside the block would be one nothing could pick
  // the key for -- and the region designated no key by name to fall back on.
  if (!envelope.names.key_public_key.empty()) {
    AppendKeyPublicKey(envelope.names.key_public_key, block_encoding, &text);
  }
  // §34.5.9 has an encrypting tool state, against the bytes subkeyword, how
  // much data the block about to be written stands for. The count is of the
  // block before any of the encoding was applied to it, so it is taken from
  // what goes into the writing rather than from the characters that come out.
  text.append(BlockEncodingDirective(block_encoding,
                                     ProtectedRegionBlockSize(envelope.body)));
  text.append("`pragma protect ").append(kDataBlockKeyword).append("=\"");
  text.append(EncryptProtectedRegion(envelope.body, region_key,
                                     block_encoding.enctype));
  text.append("\"\n");
  text.append(envelope.end_directive);
  text.append(ProtectKeywordResetDirective());
  return text;
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
// §34.5.25 gives a region a second way of stating what it is encrypted under:
// the name of the key its own keys are held under, combined with the entity
// that provided that key. A tool that encrypts is told to reach a key by
// combining those two, so a region stating only that pair is encrypted under
// what the pair reaches rather than left with nothing. The pair is consulted
// after the data's own names because a region stating both has said directly
// what its data are under, and the direct statement is what it means.
//
// §34.5.23 names the designations that entity may be combined with, and the
// public key of §34.5.26 is the second of them. It is an alternative to the
// name rather than an addition to it, so a region that wrote only a public key
// designated its key as fully as one that wrote a name, and it is reached the
// same way: against the entity written beside it.
std::string_view RegionKey(const RegionKeyNames& names,
                           std::string_view exchange_key,
                           const ProtectKeyList& keys) {
  if (keys.Empty()) return exchange_key;
  std::string_view under_data =
      keys.KeyFor(ProtectPragmaValueBody(names.data_keyowner),
                  ProtectPragmaValueBody(names.data_keyname));
  if (!under_data.empty()) return under_data;
  std::string_view owner = ProtectPragmaValueBody(names.key_keyowner);
  std::string_view under_name =
      keys.KeyFor(owner, ProtectPragmaValueBody(names.key_keyname));
  if (!under_name.empty()) return under_name;
  // The public key is the designation itself rather than a pragma_value
  // carrying one, the line that held it having already been read out of the
  // scheme it was encoded under, so nothing is stripped from it here.
  return keys.KeyFor(owner, names.key_public_key);
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
                             std::string_view region_key) {
  if (region_key.empty()) {
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
  envelope.requested_encoding = region.written_inside.encoding;
  return DecryptionEnvelopeText(envelope, region_key);
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
  return {false, DelimiterOfLine(line)};
}

}  // namespace

size_t ProtectedRegionBlockSize(std::string_view cleartext) {
  return kFingerprintBytes + cleartext.size();
}

std::string EncryptProtectedRegion(std::string_view cleartext,
                                   std::string_view key,
                                   std::string_view enctype) {
  if (key.empty()) return "";
  std::string blob = FingerprintPrefix(FingerprintOf(cleartext));
  blob.append(cleartext);
  ProtectEncoding encoding;
  encoding.enctype = std::string(enctype);
  return EncodeProtectBlock(CombineWithKey(blob, key), encoding);
}

bool DecryptProtectedBlock(std::string_view block, std::string_view key,
                           std::string* cleartext) {
  if (key.empty()) return false;
  if (block.size() < kFingerprintBytes) return false;
  std::string recovered = CombineWithKey(block, key);
  std::string_view text = std::string_view(recovered).substr(kFingerprintBytes);
  if (FingerprintOf(text) != ReadFingerprintPrefix(recovered)) return false;
  cleartext->assign(text);
  return true;
}

bool DecryptProtectedRegion(std::string_view data_block, std::string_view key,
                            std::string* cleartext, std::string_view enctype) {
  std::string block;
  if (!DecodeProtectBlock(data_block, enctype, &block)) return false;
  return DecryptProtectedBlock(block, key, cleartext);
}

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
      std::string_view region_key =
          RegionKey(in_effect.names, exchange_key, keys);
      transformed.append(ClosedRegionText(region, line, delimiter, region_key));
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
