#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

static std::vector<Token> Lex(const std::string& src) {
  static SourceManager mgr;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  return lexer.LexAll();
}

// --- §5: Source locations ---

TEST(LexerCh5, SourceLocations) {
  auto tokens = Lex("a\nb c");
  struct Case {
    size_t idx;
    int line;
    int column;
  };
  Case expected[] = {
      {0, 1, 1},
      {1, 2, 1},
      {2, 2, 3},
  };
  for (const auto& c : expected) {
    EXPECT_EQ(tokens[c.idx].loc.line, c.line) << "token " << c.idx;
    EXPECT_EQ(tokens[c.idx].loc.column, c.column) << "token " << c.idx;
  }
}
