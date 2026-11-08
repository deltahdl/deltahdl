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

size_t ScanSubkeywordChar(std::string_view list, size_t i, size_t* depth) {
  if (list[i] == '"') return SkipQuotedValue(list, i);
  if (list[i] == '(') ++*depth;
  if (list[i] == ')' && *depth > 0) --*depth;
  return i + 1;
}

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

bool IsWrittenAsString(std::string_view text) {
  return text.size() >= 2 && text.front() == '"' && text.back() == '"';
}

void ApplySubkeyword(std::string_view name, std::string_view text,
                     ProtectEncoding* encoding) {
  if (name == kEnctypeSubkeyword) {
    if (IsWrittenAsString(text)) {
      encoding->enctype = std::string(ProtectPragmaValueBody(text));
    }
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

std::string WrapLines(std::string_view text, size_t line_length) {
  if (line_length == 0 || text.size() <= line_length) return std::string(text);
  std::string wrapped;
  for (size_t i = 0; i < text.size(); i += line_length) {
    if (i != 0) wrapped.push_back('\n');
    wrapped.append(text.substr(i, line_length));
  }
  return wrapped;
}

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

bool ProtectEncodingFitsOneLine(std::string_view enctype) {
  return enctype == kBase64Enctype || enctype == kBlockEnctype;
}

ProtectEncoding DefaultProtectEncoding() {
  ProtectEncoding encoding;
  encoding.enctype = std::string(kBlockEnctype);
  return encoding;
}

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
  if (encoding.enctype.empty()) return {};
  return encoding;
}

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

std::string ProtectEncodedValueDirective(const ProtectEncoding& encoding,
                                         size_t bytes) {
  ProtectEncoding described = encoding;
  described.bytes = bytes;
  described.has_bytes = true;
  return ProtectEncodingDirective(described);
}

constexpr size_t kBase64MaxLine = 76;

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
    return WrapLines(EncodeBase64(bytes), encoding.line_length == 0
                                              ? kBase64MaxLine
                                              : encoding.line_length);
  }
  if (encoding.enctype == kBlockEnctype) {
    return WrapLines(EncodeProtectBlockAlphabet(bytes), encoding.line_length);
  }
  return {};
}

std::string EncodeProtectValue(std::string_view bytes,
                               const ProtectEncoding& encoding) {
  if (encoding.enctype == kBase64Enctype) return EncodeBase64(bytes);
  if (encoding.enctype == kBlockEnctype) {
    return EncodeProtectBlockAlphabet(bytes);
  }
  return EncodeProtectBlock(bytes, encoding);
}

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
    return DecodeBase64(text, bytes);
  }
  if (enctype == kBlockEnctype) {
    return DecodeProtectBlockAlphabet(WithoutLineBreaks(text), bytes);
  }
  return false;
}

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

bool ProtectEncodedValueHasStatedSize(const ProtectEncoding& encoding,
                                      size_t bytes) {
  return !encoding.has_bytes || encoding.bytes == bytes;
}

}  // namespace delta
