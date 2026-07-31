#include "preprocessor/protect_processing.h"

#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_keywords.h"

namespace delta {
namespace {

// The characters an encrypted region is written with. Nothing here can open a
// comment or close a string literal, so a region of arbitrary bytes survives
// being carried through source text as the value of a pragma expression.
constexpr std::string_view kEncodingAlphabet =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";

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

// Writes arbitrary bytes in the encoding alphabet, three bytes to four
// characters. A final group of one or two bytes is written in the two or three
// characters that hold it, so no padding character is needed and the encoded
// text stays inside the alphabet throughout.
std::string EncodeBlock(std::string_view bytes) {
  std::string encoded;
  encoded.reserve(((bytes.size() + 2) / 3) * 4);
  for (size_t i = 0; i < bytes.size(); i += 3) {
    size_t have = std::min<size_t>(3, bytes.size() - i);
    uint32_t group = 0;
    for (size_t n = 0; n < have; ++n) {
      auto byte = static_cast<uint32_t>(static_cast<uint8_t>(bytes[i + n]));
      group |= byte << ((2 - n) * 8);
    }
    for (size_t n = 0; n <= have; ++n) {
      encoded.push_back(kEncodingAlphabet[(group >> ((3 - n) * 6)) & 0x3FU]);
    }
  }
  return encoded;
}

// The last group of an encoded block may be short: three characters carry two
// bytes and two characters carry one. A single trailing character carries no
// whole byte, so a block that ends with one is not a block this encoding
// produced.
bool AppendDecodedTail(uint32_t group, size_t have, std::string* bytes) {
  if (have == 0) return true;
  if (have == 1) return false;
  size_t leftover = 8 - (2 * have);
  for (size_t n = 0; n + 1 < have; ++n) {
    size_t shift = leftover + ((have - 2 - n) * 8);
    bytes->push_back(static_cast<char>((group >> shift) & 0xFFU));
  }
  return true;
}

// The inverse of EncodeBlock. Returns false when the text holds a character
// the alphabet does not, or ends part way through a group, because neither can
// come out of an encoded block and both mean the value being read records
// something other than an encrypted region.
bool DecodeBlock(std::string_view text, std::string* bytes) {
  uint32_t group = 0;
  size_t have = 0;
  for (char c : text) {
    size_t index = kEncodingAlphabet.find(c);
    if (index == std::string_view::npos) return false;
    group = (group << 6) | static_cast<uint32_t>(index);
    ++have;
    if (have < 4) continue;
    for (size_t n = 0; n < 3; ++n) {
      bytes->push_back(static_cast<char>((group >> ((2 - n) * 8)) & 0xFFU));
    }
    group = 0;
    have = 0;
  }
  return AppendDecodedTail(group, have, bytes);
}

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
// envelope it produced. The standard reserves identifiers for the ciphers and
// coding schemes it specifies, and this is neither of those, so the names are
// spelled as this implementation's own rather than claiming a reserved one.
constexpr ProtectEnvelopeDescription kEnvelopeDescription{
    .encrypt_agent = "deltahdl",
    .data_method = "x-deltahdl-stream",
    .encoding = "x-deltahdl-block",
};

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
};

// Takes from `line` whatever it says about the keys a region is under. What is
// in effect where a region ends is the last writing of each name, so a later
// expression replaces an earlier one and a line writing none of them leaves
// them all as they were.
void TakeKeyNames(std::string_view line, RegionKeyNames* names) {
  std::string_view keyname = KeywordValueOnLine(line, kDataKeynameKeyword);
  if (!keyname.empty()) names->data_keyname = keyname;
  std::string_view keyowner = KeywordValueOnLine(line, kDataKeyownerKeyword);
  if (!keyowner.empty()) names->data_keyowner = keyowner;
  std::string_view digest = KeywordValueOnLine(line, kDigestKeynameKeyword);
  if (!digest.empty()) names->digest_keyname = digest;
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
  text.append(ProtectEnvelopeDescriptionDirectives(kEnvelopeDescription));
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
  text.append("`pragma protect ").append(kDataBlockKeyword).append("=\"");
  text.append(EncryptProtectedRegion(envelope.body, region_key));
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
  RegionKeyNames written_inside;
};

// The key one region's data are encrypted under. §34.5.10 has the entity a
// region names select it out of the keys supplied under the names that select
// them, so two regions naming two entities are encrypted under two keys.
//
// A user who supplied keys under no names at all supplied one key for every
// region, whoever a region names, and that key is what every region is
// encrypted under. That is the whole of what a user holding one key needs to
// say, which is why it is not the same thing as a list holding one entry.
std::string_view RegionKey(const RegionKeyNames& names,
                           std::string_view exchange_key,
                           const ProtectKeyList& keys) {
  if (keys.Empty()) return exchange_key;
  return keys.KeyFor(ProtectPragmaValueBody(names.data_keyowner),
                     ProtectPragmaValueBody(names.data_keyname));
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
  EncryptionEnvelope envelope{region.opening_directive, region.body,
                              closing_directive, region.written_inside};
  return DecryptionEnvelopeText(envelope, region_key);
}

}  // namespace

std::string EncryptProtectedRegion(std::string_view cleartext,
                                   std::string_view key) {
  if (key.empty()) return "";
  std::string blob = FingerprintPrefix(FingerprintOf(cleartext));
  blob.append(cleartext);
  return EncodeBlock(CombineWithKey(blob, key));
}

bool DecryptProtectedRegion(std::string_view data_block, std::string_view key,
                            std::string* cleartext) {
  if (key.empty()) return false;
  std::string blob;
  if (!DecodeBlock(data_block, &blob)) return false;
  if (blob.size() < kFingerprintBytes) return false;
  std::string recovered = CombineWithKey(blob, key);
  std::string_view text = std::string_view(recovered).substr(kFingerprintBytes);
  if (FingerprintOf(text) != ReadFingerprintPrefix(recovered)) return false;
  cleartext->assign(text);
  return true;
}

std::string EncryptEnvelopes(std::string_view source_text,
                             std::string_view exchange_key,
                             const ProtectKeyList& keys) {
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
  RegionKeyNames in_effect;
  bool in_envelope = false;
  for (std::string_view line : SplitLines(source_text)) {
    TakeKeyNames(line, &in_effect);
    DelimiterMatch delimiter = DelimiterOfLine(line);
    if (in_envelope && delimiter.kind == EnvelopeDelimiter::kEnd) {
      std::string_view region_key = RegionKey(in_effect, exchange_key, keys);
      transformed.append(ClosedRegionText(region, line, delimiter, region_key));
      in_envelope = false;
    } else if (in_envelope) {
      region.body.append(line);
      // What the region itself wrote is kept apart from what is merely in
      // effect over it: those are the names the envelope has to carry in the
      // clear, the rest of the region's text being about to stop being
      // readable. A name written outside the region is in the output already.
      TakeKeyNames(line, &region.written_inside);
    } else if (delimiter.kind == EnvelopeDelimiter::kBegin) {
      in_envelope = true;
      region.opening_line = line;
      region.opening_directive =
          TransformedDelimiterLine(line, delimiter, kBeginDecryptionKeyword);
      region.body.clear();
      region.written_inside = {};
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
