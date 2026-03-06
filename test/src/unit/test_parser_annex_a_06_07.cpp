#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §A.6.7 — case statements

TEST(ParserA607, CaseBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      2'b00: a = 1;\n"
      "      2'b01: a = 2;\n"
      "      default: a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCase);
  ASSERT_GE(stmt->case_items.size(), 3u);
  EXPECT_TRUE(stmt->case_items[2].is_default);
}

TEST(ParserA607, CasezStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    casez (sel)\n"
      "      4'b1???: a = 1;\n"
      "      default: a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
}

TEST(ParserA607, CasexStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    casex (sel)\n"
      "      4'b1xxx: a = 1;\n"
      "      default: a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasex);
}

TEST(ParserA607, CaseInside) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (val) inside\n"
      "      [0:5]: a = 1;\n"
      "      [6:10]: a = 2;\n"
      "      default: a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_TRUE(stmt->case_inside);
}

TEST(ParserA607, UniqueCase) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique case (sel)\n"
      "      1: a = 1;\n"
      "      2: a = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

TEST(ParserA607, PriorityCase) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority case (sel)\n"
      "      1: a = 1;\n"
      "      default: a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

TEST(ParserA607, CaseMultipleExprs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      1, 2, 3: a = 1;\n"
      "      default: a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_GE(stmt->case_items.size(), 2u);
  EXPECT_EQ(stmt->case_items[0].patterns.size(), 3u);
}

TEST(ParserA607, CaseDefaultNoColon) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      1: a = 1;\n"
      "      default a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(HasDefaultCaseItem(stmt));
}

TEST(ParserA607, Randcase) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randcase\n"
      "      50: a = 1;\n"
      "      30: a = 2;\n"
      "      20: a = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandcase);
  ASSERT_EQ(stmt->randcase_items.size(), 3u);
}

TEST(ParserA607, CaseWithBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      1: begin a = 1; b = 2; end\n"
      "      default: begin a = 0; end\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->case_items[0].body->kind, StmtKind::kBlock);
}

}  // namespace
