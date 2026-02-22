#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

static std::vector<Token> Lex(const std::string &src) {
  static SourceManager mgr;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  return lexer.LexAll();
}

// --- §11.4.13: Set membership operator (tolerance) ---

TEST(LexerCh110413, ToleranceOperators) {
  // §11.4.13: +/- (absolute tolerance) and +%- (relative tolerance).
  auto tokens = Lex("+/- +%-");
  EXPECT_EQ(tokens[0].kind, TokenKind::kPlusSlashMinus);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlusPercentMinus);
}
