#pragma once

#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_design.h"

namespace delta {

class ScopePrefixRecord {
 public:
  void Read(const Token& tok,
            const std::unordered_set<std::string_view>& types);
  void Forget(SourceLoc loc);
  std::vector<ScopePrefix> Take();

 private:
  std::vector<ScopePrefix> prefixes_;
  SourceLoc furthest_;
  Token last_;
  TokenKind before_last_ = TokenKind::kEof;
};

}  // namespace delta
