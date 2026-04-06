#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(CaseMatchesSyntaxParsing, PatternParenthesized) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (e matches (tagged Valid .n)) x = n;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CaseMatchesSyntaxParsing, CaseMatchesKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (sel) matches\n"
      "      8'd5: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_TRUE(stmt->case_matches);
  EXPECT_FALSE(stmt->case_inside);
}

TEST(CaseMatchesSyntaxParsing, CaseMatchesWithGuard) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (sel) matches\n"
      "      8'd5 &&& guard: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_matches);
  ASSERT_GE(stmt->case_items.size(), 1u);
  auto* pat = stmt->case_items[0].patterns[0];
  EXPECT_EQ(pat->kind, ExprKind::kBinary);
  EXPECT_EQ(pat->op, TokenKind::kAmpAmpAmp);
}

TEST(CaseMatchesSyntaxParsing, CasezMatches) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    casez (sel) matches\n"
      "      4'b1???: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_matches);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
}

TEST(CaseMatchesSyntaxParsing, CasexMatches) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    casex (sel) matches\n"
      "      4'b1???: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_matches);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasex);
}

TEST(CaseMatchesSyntaxParsing, CaseInsideAndMatchesMutualExclusion) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (sel) inside matches\n"
      "      8'd5: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(CaseMatchesSyntaxParsing, CaseMatchesEmptyNoItems) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (sel) matches\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->case_matches);
  EXPECT_EQ(stmt->case_items.size(), 0u);
}

}  // namespace
