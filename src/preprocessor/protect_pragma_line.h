#pragma once

#include <cstddef>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

namespace delta {

std::string_view TrimLeading(std::string_view text);
std::string_view TrimTrailing(std::string_view text);

bool ProtectPragmaLine(std::string_view line, std::string_view* body);

size_t SkipStringValue(std::string_view body, size_t i);

bool StartsLineComment(std::string_view body, size_t i);

struct ListedKeyword {
  std::string_view name;
  bool has_value;
  std::string_view value;
};

std::vector<ListedKeyword> TopLevelKeywords(std::string_view body);

std::string_view KeywordValueOnLine(std::string_view line,
                                    std::string_view keyword);

bool IsParenthesizedPragmaValue(std::string_view value);

std::string_view KeywordSingleValueOnLine(std::string_view line,
                                          std::string_view keyword);

bool NamesBareKeyword(std::string_view line, std::string_view keyword);

bool NamesKeyword(std::string_view line, std::string_view keyword);

std::string_view ListedExpressionText(std::string_view body,
                                      const ListedKeyword& listed);

std::string ProtectDirectiveWriting(
    const std::vector<std::string_view>& expressions);

bool ResetsProtectPragmaLine(std::string_view line);

std::optional<std::string> ProtectLineAfterLastReset(std::string_view line);

}  // namespace delta
