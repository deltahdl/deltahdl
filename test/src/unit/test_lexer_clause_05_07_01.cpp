#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

// --- §5.7.1: Integer literal constants ---

TEST(LexerCh50701, NoDigitsAfterBaseError) {
  // §5.7.1: A plus or minus operator between the base format and the
  // number is illegal syntax.
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", "8'd-6");
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  EXPECT_TRUE(diag.HasErrors());
}

TEST(LexerCh50701, DecimalXZMixedError) {
  // §5.7.1: Decimal literal shall not contain x/z unless exactly one digit.
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", "8'd1x");
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  EXPECT_TRUE(diag.HasErrors());
}

TEST(LexerCh50701, DecimalXZMultiError) {
  // §5.7.1: Multiple x/z digits in decimal is invalid.
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", "8'dxz");
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  EXPECT_TRUE(diag.HasErrors());
}
