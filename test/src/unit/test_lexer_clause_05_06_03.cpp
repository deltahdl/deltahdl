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

// --- §5.6.3: System tasks and system functions ---

TEST(LexerCh50603, EmbeddedDollar) {
  // §5.6.3: system_tf_identifier allows $ within the name.
  auto tokens = Lex("$test$plusargs $value$plusargs");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$test$plusargs");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[1].text, "$value$plusargs");
}

TEST(LexerCh50603, DollarAloneIsNotSystemIdentifier) {
  // §5.6.3: Grammar requires >= 1 char after $; bare $ is kDollar.
  auto tokens = Lex("$");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
}
