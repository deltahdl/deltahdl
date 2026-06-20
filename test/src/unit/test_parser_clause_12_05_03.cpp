#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §12.5.3 (N1): the parser attaches a CaseQualifier of kUnique, kUnique0, or
// kPriority to a case statement whose keyword is preceded by the
// corresponding qualifier keyword.

TEST(CaseQualifierParsing, UniqueAttachedToCase) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique case (sel)\n"
      "      2'b00: a = 1;\n"
      "      2'b01: a = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

TEST(CaseQualifierParsing, Unique0AttachedToCase) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique0 case (sel)\n"
      "      2'b00: a = 1;\n"
      "      2'b01: a = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
}

TEST(CaseQualifierParsing, PriorityAttachedToCase) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority case (sel)\n"
      "      2'b00: a = 1;\n"
      "      2'b01: a = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

TEST(CaseQualifierParsing, UniqueAttachedToCasez) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique casez (sel)\n"
      "      2'b1?: a = 1;\n"
      "      default: a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

TEST(CaseQualifierParsing, PriorityAttachedToCasex) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority casex (sel)\n"
      "      2'b1x: a = 1;\n"
      "      default: a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasex);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

TEST(CaseQualifierParsing, Unique0AttachedToCasex) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique0 casex (sel)\n"
      "      2'b1x: a = 1;\n"
      "      default: a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasex);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
}

TEST(CaseQualifierParsing, UnqualifiedCaseHasNoneQualifier) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      2'b00: a = 1;\n"
      "      default: a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kNone);
}

}  // namespace
