#include "parser/scope_prefix_record.h"

#include <string_view>
#include <tuple>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_design.h"

namespace delta {

// Whether `a` stands before `b` in the one text a parse reads.
static bool Before(SourceLoc a, SourceLoc b) {
  return std::tie(a.line, a.column) < std::tie(b.line, b.column);
}

static bool IsName(TokenKind kind) {
  return kind == TokenKind::kIdentifier ||
         kind == TokenKind::kEscapedIdentifier;
}

void ScopePrefixRecord::Read(
    const Token& tok, const std::unordered_set<std::string_view>& types) {
  if (!Before(furthest_, tok.loc)) return;
  furthest_ = tok.loc;
  if (tok.kind == TokenKind::kColonColon && IsName(last_.kind) &&
      before_last_ != TokenKind::kColonColon && types.count(last_.text) == 0) {
    prefixes_.push_back({last_.text, last_.loc});
  }
  before_last_ = last_.kind;
  last_ = tok;
}

void ScopePrefixRecord::Forget(SourceLoc loc) {
  std::erase_if(prefixes_, [loc](const ScopePrefix& prefix) {
    return std::tie(prefix.loc.line, prefix.loc.column) ==
           std::tie(loc.line, loc.column);
  });
}

std::vector<ScopePrefix> ScopePrefixRecord::Take() {
  return std::move(prefixes_);
}

}  // namespace delta
