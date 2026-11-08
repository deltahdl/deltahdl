#include "preprocessor/protect_pragma_line.h"

#include <cctype>
#include <cstddef>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/standard_pragmas.h"

namespace delta {
namespace {

bool IsIdentifierChar(char c) {
  return std::isalnum(static_cast<unsigned char>(c)) != 0 || c == '_' ||
         c == '$';
}

bool IsIdentifierStart(char c) {
  return std::isalpha(static_cast<unsigned char>(c)) != 0 || c == '_';
}

bool ConsumeWord(std::string_view& text, std::string_view word) {
  if (text.substr(0, word.size()) != word) return false;
  std::string_view rest = text.substr(word.size());
  if (!rest.empty() && IsIdentifierChar(rest.front())) return false;
  text = rest;
  return true;
}

size_t SkipParenGroup(std::string_view body, size_t i) {
  size_t depth = 0;
  while (i < body.size()) {
    if (body[i] == '(') ++depth;
    if (body[i] == ')' && --depth == 0) return i + 1;
    ++i;
  }
  return i;
}

size_t SkipEscapedIdentifier(std::string_view body, size_t i) {
  ++i;
  while (i < body.size() &&
         std::isspace(static_cast<unsigned char>(body[i])) == 0) {
    ++i;
  }
  return i;
}

struct OpenValue {
  bool open;
  size_t start;
};

void CloseValue(std::string_view body, size_t end, OpenValue* value,
                std::vector<ListedKeyword>* keywords) {
  if (!value->open) return;
  value->open = false;
  if (keywords->empty()) return;
  keywords->back().value =
      TrimTrailing(TrimLeading(body.substr(value->start, end - value->start)));
}

size_t ScanKeyword(std::string_view body, size_t i, bool in_value,
                   std::vector<ListedKeyword>* keywords) {
  size_t start = i;
  while (i < body.size() && IsIdentifierChar(body[i])) ++i;
  if (!in_value) {
    keywords->push_back({body.substr(start, i - start), false, {}});
  }
  return i;
}

void MarkLastKeywordValued(std::vector<ListedKeyword>* keywords) {
  if (!keywords->empty()) keywords->back().has_value = true;
}

}  // namespace

std::string_view TrimLeading(std::string_view text) {
  size_t i = 0;
  while (i < text.size() && std::isspace(static_cast<unsigned char>(text[i]))) {
    ++i;
  }
  return text.substr(i);
}

std::string_view TrimTrailing(std::string_view text) {
  size_t end = text.size();
  while (end > 0 && std::isspace(static_cast<unsigned char>(text[end - 1]))) {
    --end;
  }
  return text.substr(0, end);
}

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
    } else if (c == '\\') {
      i = SkipEscapedIdentifier(body, i);
    } else if (IsIdentifierStart(c)) {
      i = ScanKeyword(body, i, in_value, &keywords);
    } else {
      ++i;
    }
  }
  CloseValue(body, i, &value, &keywords);
  return keywords;
}

std::string_view KeywordValueOnLine(std::string_view line,
                                    std::string_view keyword) {
  std::string_view body;
  if (!ProtectPragmaLine(line, &body)) return {};
  std::string_view value;
  for (const ListedKeyword& listed : TopLevelKeywords(body)) {
    if (listed.name == keyword && listed.has_value) value = listed.value;
  }
  return value;
}

bool IsParenthesizedPragmaValue(std::string_view value) {
  return !value.empty() && value.front() == '(';
}

std::string_view KeywordSingleValueOnLine(std::string_view line,
                                          std::string_view keyword) {
  std::string_view value = KeywordValueOnLine(line, keyword);
  if (IsParenthesizedPragmaValue(value)) return {};
  return value;
}

bool NamesBareKeyword(std::string_view line, std::string_view keyword) {
  std::string_view body;
  if (!ProtectPragmaLine(line, &body)) return false;
  for (const ListedKeyword& listed : TopLevelKeywords(body)) {
    if (listed.name == keyword && !listed.has_value) return true;
  }
  return false;
}

bool NamesKeyword(std::string_view line, std::string_view keyword) {
  std::string_view body;
  if (!ProtectPragmaLine(line, &body)) return false;
  for (const ListedKeyword& listed : TopLevelKeywords(body)) {
    if (listed.name == keyword) return true;
  }
  return false;
}

std::string_view ListedExpressionText(std::string_view body,
                                      const ListedKeyword& listed) {
  if (!listed.has_value) return listed.name;
  auto starts = static_cast<size_t>(listed.name.data() - body.data());
  auto ends = static_cast<size_t>(listed.value.data() - body.data()) +
              listed.value.size();
  return body.substr(starts, ends - starts);
}

std::string ProtectDirectiveWriting(
    const std::vector<std::string_view>& expressions) {
  if (expressions.empty()) return {};
  std::string directive = "`pragma protect ";
  for (size_t n = 0; n < expressions.size(); ++n) {
    if (n != 0) directive.append(", ");
    directive.append(expressions[n]);
  }
  directive.push_back('\n');
  return directive;
}

bool ResetsProtectPragmaLine(std::string_view line) {
  std::string_view rest = TrimLeading(line);
  if (rest.substr(0, 1) != "`") return false;
  rest.remove_prefix(1);
  if (!ConsumeWord(rest, "pragma")) return false;
  rest = TrimLeading(rest);
  if (ConsumeWord(rest, kResetallPragmaName)) return true;
  if (!ConsumeWord(rest, kResetPragmaName)) return false;
  for (const ListedKeyword& listed : TopLevelKeywords(rest)) {
    if (listed.name == kProtectPragmaName) return true;
  }
  return false;
}

std::optional<std::string> ProtectLineAfterLastReset(std::string_view line) {
  std::string_view body;
  if (!ProtectPragmaLine(line, &body)) return std::nullopt;
  std::optional<std::string_view> after;
  for (const ListedKeyword& listed : TopLevelKeywords(body)) {
    if (listed.name != kResetKeyword || listed.has_value) continue;
    after = body.substr(static_cast<size_t>(listed.name.data() - body.data()) +
                        listed.name.size());
  }
  if (!after.has_value()) return std::nullopt;
  std::string_view rest = TrimLeading(*after);
  if (rest.substr(0, 1) == ",") rest = TrimLeading(rest.substr(1));
  std::string directive = "`pragma protect ";
  directive.append(rest);
  return directive;
}

}  // namespace delta
