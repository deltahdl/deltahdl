#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

// --- §5.6.4: Compiler directives ---

TEST(LexerCh50604, BacktickIsUnexpected) {
  // §5.6.4: Backtick introduces compiler directives; if it reaches the
  // lexer (not consumed by preprocessor), it is an error.
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", "`define FOO 1");
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tokens = lexer.LexAll();
  EXPECT_TRUE(diag.HasErrors());
}
