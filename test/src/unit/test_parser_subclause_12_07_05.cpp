#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;
namespace {

TEST(LoopSyntaxParsing, DoWhileSingleStatementBody) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    do x = x + 1; while (x < 10);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_NE(stmt->condition, nullptr);
}

TEST(LoopSyntaxParsing, DoWhileNullStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin do ; while (x > 0); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
}

TEST(LoopSyntaxParsing, DoWhileBlockBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    do begin x = x + 1; end while (x < 10);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

TEST(LoopSyntaxParsing, ErrorDoWhileMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    do x = x + 1; while (x < 10)\n"
      "  end\n"
      "endmodule\n");
  // The `end` on line 4 is the token standing where §12.7.5 requires the ';'.
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got 'end'", 4, "12.7.5"));
}

TEST(LoopSyntaxParsing, ErrorDoWhileMissingWhileKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    do x = x + 1; (x < 10);\n"
      "  end\n"
      "endmodule\n");
  // The '(' stands where §12.7.5 requires the `while` that closes a do loop.
  EXPECT_TRUE(ReportedError(r.diags, "expected 'while', got '('", 3, "12.7.5"));
}

TEST(LoopSyntaxParsing, ErrorDoWhileMissingOpenParen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    do x = x + 1; while x < 10);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '(', got identifier", 3, "12.7.5"));
}

TEST(LoopSyntaxParsing, ErrorDoWhileMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    do x = x + 1; while (x < 10;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ';'", 3, "12.7.5"));
}

}  // namespace
