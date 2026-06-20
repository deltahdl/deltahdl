#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(IfMatchesParsing, IfMatchesBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x matches 8'd5) y = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->condition->op, TokenKind::kKwMatches);
}

TEST(IfMatchesParsing, IfMatchesWithGuard) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x matches 8'd5 &&& en) y = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->condition->op, TokenKind::kAmpAmpAmp);
}

TEST(IfMatchesParsing, IfMatchesWithElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x matches 8'd5) y = 1;\n"
      "    else y = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->else_body, nullptr);
}

TEST(IfMatchesParsing, IfMatchesElseIfChain) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x matches 8'd1) y = 1;\n"
      "    else if (x matches 8'd2) y = 2;\n"
      "    else y = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
