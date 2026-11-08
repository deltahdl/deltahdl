#pragma once

#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_covergroup.h"

namespace delta {

class DiagEngine;

inline bool IsBinsKeyword(TokenKind k) {
  return k == TokenKind::kKwBins || k == TokenKind::kKwIllegalBins ||
         k == TokenKind::kKwIgnoreBins;
}

inline bool IsOptionKeyword(const Token& t) {
  return t.Is(TokenKind::kIdentifier) &&
         (t.text == "option" || t.text == "type_option");
}

struct CovergroupBodyState {
  CovergroupDecl* cg = nullptr;
  std::unordered_set<std::string> seen_options;
  std::vector<std::string_view> formals;
  std::unordered_set<std::string_view> names;
};

void ReportStrayCoverageToken(const Token& stray, DiagEngine& diag);

void ReportUnnamedBin(SourceLoc at, DiagEngine& diag);

inline BinsKeyword BinsKeywordOf(TokenKind k) {
  if (k == TokenKind::kKwIllegalBins) return BinsKeyword::kIllegalBins;
  if (k == TokenKind::kKwIgnoreBins) return BinsKeyword::kIgnoreBins;
  return BinsKeyword::kBins;
}

}  // namespace delta
