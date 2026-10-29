#pragma once

#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_design.h"

namespace delta {

// §3.12 (printed page 55): the prefixes of the scoped names a parse reads, each
// an identifier with a scope resolution operator after it and none before it.
// The parser reads some tokens more than once, backing up to try another
// production, and peeking ahead would move the reading position a file path
// specification is read from, so the record weighs each token on its first
// read alone, as it is consumed. Every position is first read in the order of
// the text, so the two tokens first read before a `::` are the two written
// before it.
class ScopePrefixRecord {
 public:
  // Notes `tok`, the token the parser has just consumed, adding the identifier
  // before it when `tok` is a `::` read for the first time and `types`, the
  // type names the parser knows where it stands, does not hold the identifier:
  // a class's scope is no package's.
  void Read(const Token& tok,
            const std::unordered_set<std::string_view>& types);
  // Drops the prefix read at `loc`, an import or export declaration's package
  // name, which §26.3's own check reads.
  void Forget(SourceLoc loc);
  std::vector<ScopePrefix> Take();

 private:
  std::vector<ScopePrefix> prefixes_;
  // The position of the furthest token read, and the two tokens first read
  // last, the latest first.
  SourceLoc furthest_;
  Token last_;
  TokenKind before_last_ = TokenKind::kEof;
};

}  // namespace delta
