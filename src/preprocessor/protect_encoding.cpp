#include "preprocessor/protect_encoding.h"

#include <cctype>
#include <cstddef>
#include <span>
#include <string>
#include <string_view>
#include <vector>

#include "preprocessor/protect_encoding_codecs.h"
#include "preprocessor/protect_keywords.h"

namespace delta {
namespace {

// Table 34-2, in the order the table lists them: the identifier, whether every
// implementation provides the scheme behind it, and the published algorithm
// that identifier stands for.
//
// The two marked required are the ones a tool may be handed a block in without
// having been told anything about the tool that wrote it. The two marked
// optional are provided here as well, which the table permits and does not
// require: what it requires of an implementation offering them is that it
// offer them under these names rather than under names of its own.
constexpr ProtectEncodingAlgorithm kProtectEncodingAlgorithms[] = {
    {kUuencodeEnctype, true, "IEEE Std 1003.1, the historical uuencode"},
    {kBase64Enctype, true, "IETF RFC 2045, also IEEE Std 1003.1 uuencode -m"},
    {kQuotedPrintableEnctype, false, "IETF RFC 2045"},
    {kRawEnctype, false,
     "the identity transformation, which performs no encoding and leaves the "
     "data free to hold characters that cannot be printed"},
};

std::string_view TrimSpace(std::string_view text) {
  size_t begin = 0;
  while (begin < text.size() &&
         std::isspace(static_cast<unsigned char>(text[begin])) != 0) {
    ++begin;
  }
  size_t end = text.size();
  while (end > begin &&
         std::isspace(static_cast<unsigned char>(text[end - 1])) != 0) {
    --end;
  }
  return text.substr(begin, end - begin);
}

// Advances past a value written in quotes, returning the index just after the
// quotation mark that closes the one opening at `i`. A quotation mark written
// behind a backslash is content of the value rather than its end.
size_t SkipQuotedValue(std::string_view text, size_t i) {
  ++i;
  while (i < text.size()) {
    if (text[i] == '\\' && i + 1 < text.size()) {
      i += 2;
      continue;
    }
    if (text[i] == '"') return i + 1;
    ++i;
  }
  return i;
}

// Advances one position of the list, keeping track of how deeply nested in
// parentheses the walk is, and stepping over a quoted value whole. A comma
// inside either belongs to whatever is written there rather than to the list
// being split.
size_t ScanSubkeywordChar(std::string_view list, size_t i, size_t* depth) {
  if (list[i] == '"') return SkipQuotedValue(list, i);
  if (list[i] == '(') ++*depth;
  if (list[i] == ')' && *depth > 0) --*depth;
  return i + 1;
}

// The expressions of the subkeyword list, one per element, as they were
// written. Splitting on the commas of the list's own level is what keeps a
// value that happens to hold a comma from being read as two expressions.
std::vector<std::string_view> SplitSubkeywordList(std::string_view list) {
  std::vector<std::string_view> items;
  size_t start = 0;
  size_t depth = 0;
  size_t i = 0;
  while (i < list.size()) {
    if (list[i] == ',' && depth == 0) {
      items.push_back(list.substr(start, i - start));
      start = i + 1;
      ++i;
      continue;
    }
    i = ScanSubkeywordChar(list, i, &depth);
  }
  items.push_back(list.substr(start));
  return items;
}

// The count a <number> subkeyword carries. §34.5.9.1 writes both of them as
// numbers, so text spelled any other way carries no count and is not one.
bool ParseCount(std::string_view text, size_t* value) {
  if (text.empty()) return false;
  size_t count = 0;
  for (char c : text) {
    if (c < '0' || c > '9') return false;
    count = (count * 10) + static_cast<size_t>(c - '0');
  }
  *value = count;
  return true;
}

// Applies one expression of the subkeyword list. A name §34.5.9.1 does not
// define qualifies the value with something this subclause says nothing about,
// so nothing is taken from it.
void ApplySubkeyword(std::string_view name, std::string_view text,
                     ProtectEncoding* encoding) {
  if (name == kEnctypeSubkeyword) {
    encoding->enctype = std::string(ProtectPragmaValueBody(text));
    return;
  }
  if (name == kLineLengthSubkeyword) {
    ParseCount(text, &encoding->line_length);
    return;
  }
  if (name == kBytesSubkeyword) {
    encoding->has_bytes = ParseCount(text, &encoding->bytes);
  }
}

// Breaks `text` so that no line of it runs past `line_length` characters. A
// length of none leaves the text on the single line it was written as.
std::string WrapLines(std::string_view text, size_t line_length) {
  if (line_length == 0 || text.size() <= line_length) return std::string(text);
  std::string wrapped;
  for (size_t i = 0; i < text.size(); i += line_length) {
    if (i != 0) wrapped.push_back('\n');
    wrapped.append(text.substr(i, line_length));
  }
  return wrapped;
}

// The same text with the breaks taken back out, for a scheme whose own reading
// has no place for them.
std::string WithoutLineBreaks(std::string_view text) {
  std::string joined;
  joined.reserve(text.size());
  for (char c : text) {
    if (c != '\n' && c != '\r') joined.push_back(c);
  }
  return joined;
}

const ProtectEncodingAlgorithm* FindProtectEncodingAlgorithm(
    std::string_view enctype) {
  for (const ProtectEncodingAlgorithm& algorithm : kProtectEncodingAlgorithms) {
    if (algorithm.enctype == enctype) return &algorithm;
  }
  return nullptr;
}

}  // namespace

std::span<const ProtectEncodingAlgorithm> ProtectEncodingAlgorithms() {
  return kProtectEncodingAlgorithms;
}

bool IsProtectEncodingAlgorithm(std::string_view enctype) {
  return FindProtectEncodingAlgorithm(enctype) != nullptr;
}

bool IsRequiredProtectEncodingAlgorithm(std::string_view enctype) {
  const ProtectEncodingAlgorithm* algorithm =
      FindProtectEncodingAlgorithm(enctype);
  return algorithm != nullptr && algorithm->required;
}

bool ProtectEncodingIsAvailable(std::string_view enctype) {
  return IsProtectEncodingAlgorithm(enctype) || enctype == kBlockEnctype;
}

// The identity transformation writes whatever the data hold, and the two
// line-oriented schemes write a quotation mark for one byte in sixty-four and
// break their output into lines besides. What is left are the two that write a
// long run of characters drawn from an alphabet holding neither.
bool ProtectEncodingFitsPragmaValue(std::string_view enctype) {
  return enctype == kBase64Enctype || enctype == kBlockEnctype;
}

ProtectEncoding DefaultProtectEncoding() {
  ProtectEncoding encoding;
  encoding.enctype = std::string(kBlockEnctype);
  return encoding;
}

// The parentheses are stepped over rather than required, because the same list
// reaches here both as the pragma_value a directive wrote and as the list
// inside it, and the two describe one encoding.
ProtectEncoding ParseProtectEncoding(std::string_view value) {
  ProtectEncoding encoding;
  std::string_view list = TrimSpace(value);
  if (list.size() >= 2 && list.front() == '(' && list.back() == ')') {
    list = TrimSpace(list.substr(1, list.size() - 2));
  }
  for (std::string_view item : SplitSubkeywordList(list)) {
    size_t equals = item.find('=');
    if (equals == std::string_view::npos) continue;
    ApplySubkeyword(TrimSpace(item.substr(0, equals)),
                    TrimSpace(item.substr(equals + 1)), &encoding);
  }
  return encoding;
}

// The enctype is written whatever the descriptor holds, it being the one
// subkeyword §34.5.9.1 requires; the other two are written only where the
// descriptor carries them, an omitted optional being what says a text stated
// no length and no count rather than stated them as zero.
std::string ProtectEncodingValue(const ProtectEncoding& encoding) {
  std::string text = "(";
  text.append(kEnctypeSubkeyword).append("=\"").append(encoding.enctype);
  text.append("\"");
  if (encoding.line_length != 0) {
    text.append(", ").append(kLineLengthSubkeyword).append("=");
    text.append(std::to_string(encoding.line_length));
  }
  if (encoding.has_bytes) {
    text.append(", ").append(kBytesSubkeyword).append("=");
    text.append(std::to_string(encoding.bytes));
  }
  text.append(")");
  return text;
}

std::string ProtectEncodingDirective(const ProtectEncoding& encoding) {
  std::string text = "`pragma protect ";
  text.append(kEncodingKeyword).append("=");
  text.append(ProtectEncodingValue(encoding)).append("\n");
  return text;
}

// The identity transformation is the one scheme a line length asks nothing of.
// Table 34-2 has it perform no encoding at all, so there is no encoded text
// standing beside the data to be broken, and a break put in would be a byte
// the data never held.
std::string EncodeProtectBlock(std::string_view bytes,
                               const ProtectEncoding& encoding) {
  if (encoding.enctype == kRawEnctype) return std::string(bytes);
  if (encoding.enctype == kUuencodeEnctype) {
    return EncodeUuencode(bytes, encoding.line_length);
  }
  if (encoding.enctype == kQuotedPrintableEnctype) {
    return EncodeQuotedPrintable(bytes, encoding.line_length);
  }
  if (encoding.enctype == kBase64Enctype) {
    return WrapLines(EncodeBase64(bytes), encoding.line_length);
  }
  if (encoding.enctype == kBlockEnctype) {
    return WrapLines(EncodeProtectBlockAlphabet(bytes), encoding.line_length);
  }
  return {};
}

// The two line-oriented schemes are handed the text as it stands, a line
// meaning something to each of them, and the identity transformation is handed
// it as it stands because there every byte is data. What is left are the two
// that write one long run of characters, and there a break was put in by the
// writing rather than by the data.
bool DecodeProtectBlock(std::string_view text, std::string_view enctype,
                        std::string* bytes) {
  if (enctype == kRawEnctype) {
    bytes->assign(text);
    return true;
  }
  if (enctype == kUuencodeEnctype) return DecodeUuencode(text, bytes);
  if (enctype == kQuotedPrintableEnctype) {
    return DecodeQuotedPrintable(text, bytes);
  }
  if (enctype == kBase64Enctype) {
    return DecodeBase64(WithoutLineBreaks(text), bytes);
  }
  if (enctype == kBlockEnctype) {
    return DecodeProtectBlockAlphabet(WithoutLineBreaks(text), bytes);
  }
  return false;
}

// The scheme is asked about before the text is, because a scheme nothing here
// provides makes the question about the text unanswerable rather than answers
// it: there is no writing to measure the characters against, so nothing can be
// concluded about whether they came out of one.
ProtectEncodedValueRead ReadProtectEncodedValue(std::string_view text,
                                                const ProtectEncoding& encoding,
                                                std::string* bytes) {
  if (!ProtectEncodingIsAvailable(encoding.enctype)) {
    return ProtectEncodedValueRead::kSchemeUnavailable;
  }
  if (!DecodeProtectBlock(text, encoding.enctype, bytes)) {
    return ProtectEncodedValueRead::kNotWrittenInScheme;
  }
  return ProtectEncodedValueRead::kRead;
}

}  // namespace delta
