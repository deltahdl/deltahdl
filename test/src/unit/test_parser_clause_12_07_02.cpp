#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(LoopSyntaxParsing, RepeatLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    repeat(10) @(posedge clk);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRepeat);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(LoopSyntaxParsing, RepeatWithBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    repeat(5) begin\n"
      "      a = a + 1;\n"
      "      @(posedge clk);\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRepeat);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

TEST(LoopSyntaxParsing, RepeatWithExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    repeat (n + 1) begin\n"
      "      x = x + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRepeat);
  EXPECT_NE(stmt->condition, nullptr);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

TEST(LoopSyntaxParsing, RepeatNullStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin repeat (5) ; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRepeat);
}

TEST(LoopSyntaxParsing, ErrorRepeatMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    repeat (10 x = x + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(LoopSyntaxParsing, RepeatAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    repeat (3) a = a + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRepeat);
}

}  // namespace
