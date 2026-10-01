#pragma once

#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "lexer/token.h"
#include "parser/ast_covergroup.h"

namespace delta {

// The token tests the covergroup body readers in parser_covergroup.cpp and
// parser_covergroup_cross.cpp share (A.2.11).

inline bool IsBinsKeyword(TokenKind k) {
  return k == TokenKind::kKwBins || k == TokenKind::kKwIllegalBins ||
         k == TokenKind::kKwIgnoreBins;
}

// `option` and `type_option` are identifiers the grammar gives a meaning only
// where a coverage_option stands (§19.7).
inline bool IsOptionKeyword(const Token& t) {
  return t.Is(TokenKind::kIdentifier) &&
         (t.text == "option" || t.text == "type_option");
}

// The state one covergroup body is read with (§19.3): its tree, the option
// assignments its own level has made (§19.7), the names of its formals and of
// its sample method's formals (§19.7.1, §19.8.1), and the names its
// coverpoints and crosses have taken (§19.5).
struct CovergroupBodyState {
  CovergroupDecl* cg = nullptr;
  std::unordered_set<std::string> seen_options;
  std::vector<std::string_view> formals;
  std::vector<std::string_view> sample_formals;
  std::unordered_set<std::string_view> names;
};

inline BinsKeyword BinsKeywordOf(TokenKind k) {
  if (k == TokenKind::kKwIllegalBins) return BinsKeyword::kIllegalBins;
  if (k == TokenKind::kKwIgnoreBins) return BinsKeyword::kIgnoreBins;
  return BinsKeyword::kBins;
}

}  // namespace delta
