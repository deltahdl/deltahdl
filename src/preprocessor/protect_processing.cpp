#include "preprocessor/protect_processing.h"

#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "preprocessor/protect_envelope.h"

namespace delta {
namespace {

// The characters an encrypted region is written with. Nothing here can open a
// comment or close a string literal, so a region of arbitrary bytes survives
// being carried through source text as the value of a pragma expression.
constexpr std::string_view kEncodingAlphabet =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";

// The two expressions that delimit an encryption envelope, and the two that
// delimit the decryption envelope it is transformed into.
constexpr std::string_view kBeginEncryptionKeyword = "begin";
constexpr std::string_view kEndEncryptionKeyword = "end";
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

// Scans the identifier starting at `i`, collecting it when it names an
// expression of the list rather than qualifying a value, and returns the index
// just past it.
size_t ScanKeyword(std::string_view body, size_t i, bool in_value,
                   std::vector<std::string_view>* keywords) {
  size_t start = i;
  while (i < body.size() && IsIdentifierChar(body[i])) ++i;
  if (!in_value) keywords->push_back(body.substr(start, i - start));
  return i;
}

// The keywords a directive's expression list names at its own level, in
// writing order. A word inside a parenthesized value, one inside a string, and
// one standing on the right of an '=' all qualify a value rather than naming
// an expression of the list, so none of them is collected. A one-line comment
// is not part of the list at all and ends the walk.
std::vector<std::string_view> TopLevelKeywords(std::string_view body) {
  std::vector<std::string_view> keywords;
  size_t i = 0;
  bool in_value = false;
  while (i < body.size()) {
    char c = body[i];
    if (StartsLineComment(body, i)) {
      break;
    } else if (c == '(') {
      i = SkipParenGroup(body, i);
    } else if (c == '"') {
      i = SkipStringValue(body, i);
    } else if (c == ',') {
      in_value = false;
      ++i;
    } else if (c == '=') {
      in_value = true;
      ++i;
    } else if (IsIdentifierStart(c)) {
      i = ScanKeyword(body, i, in_value, &keywords);
    } else {
      ++i;
    }
  }
  return keywords;
}

// Which of the two encryption envelope delimiters a directive line carries.
enum class EnvelopeDelimiter : uint8_t { kNone, kBegin, kEnd };

EnvelopeDelimiter DelimiterOf(std::string_view body) {
  for (std::string_view keyword : TopLevelKeywords(body)) {
    if (keyword == kBeginEncryptionKeyword) return EnvelopeDelimiter::kBegin;
    if (keyword == kEndEncryptionKeyword) return EnvelopeDelimiter::kEnd;
  }
  return EnvelopeDelimiter::kNone;
}

EnvelopeDelimiter DelimiterOfLine(std::string_view line) {
  std::string_view body;
  if (!ProtectPragmaLine(line, &body)) return EnvelopeDelimiter::kNone;
  return DelimiterOf(body);
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

// The decryption envelope one encryption envelope's body is transformed into:
// the pair of expressions that delimits a protected region, with the encrypted
// body recorded on an expression between them. The region's own text does not
// appear.
std::string DecryptionEnvelopeText(std::string_view body,
                                   std::string_view key) {
  std::string text;
  text.append("`pragma protect ").append(kBeginDecryptionKeyword).append("\n");
  text.append("`pragma protect ").append(kDataBlockKeyword).append("=\"");
  text.append(EncryptProtectedRegion(body, key)).append("\"\n");
  text.append("`pragma protect ").append(kEndDecryptionKeyword).append("\n");
  return text;
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
                             std::string_view key) {
  // Without a key there is nothing to encrypt a region under, so the text
  // stands as it is written.
  if (key.empty()) return std::string(source_text);
  std::string transformed;
  std::string body;
  bool in_envelope = false;
  for (std::string_view line : SplitLines(source_text)) {
    EnvelopeDelimiter delimiter = DelimiterOfLine(line);
    if (in_envelope && delimiter == EnvelopeDelimiter::kEnd) {
      transformed.append(DecryptionEnvelopeText(body, key));
      in_envelope = false;
    } else if (in_envelope) {
      body.append(line);
    } else if (delimiter == EnvelopeDelimiter::kBegin) {
      in_envelope = true;
      body.clear();
    } else {
      transformed.append(line);
    }
  }
  // A region whose closing expression was never written closes no envelope, so
  // what it gathered is text of the source rather than a body to encrypt.
  if (in_envelope) transformed.append(body);
  return transformed;
}

}  // namespace delta
