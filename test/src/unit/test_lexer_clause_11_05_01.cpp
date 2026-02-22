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

// --- §11.5.1: Vector bit-select and part-select addressing ---

TEST(LexerCh11501, IndexedPartSelectOperators) {
  // §11.5.1: +: and -: for indexed part-selects.
  auto tokens = Lex("+: -:");
  EXPECT_EQ(tokens[0].kind, TokenKind::kPlusColon);
  EXPECT_EQ(tokens[1].kind, TokenKind::kMinusColon);
}
