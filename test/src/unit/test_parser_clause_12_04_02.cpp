#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(QualifiedIfParsing, Unique0IfChainElseIf) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    unique0 if (a == 0) x = 0;\n"
      "    else if (a == 1) x = 1;\n"
      "    else if (a == 2) x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
}

TEST(QualifiedIfParsing, PriorityIfWithElse) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    priority if (a[2:1] == 0) x = 0;\n"
      "    else if (a[2] == 0) x = 1;\n"
      "    else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);

  ASSERT_NE(stmt->else_branch, nullptr);
  ASSERT_NE(stmt->else_branch->else_branch, nullptr);
}

TEST(QualifiedIfParsing, UniqueIfInAlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] out;\n"
      "  always_comb begin\n"
      "    unique if (sel == 2'b00)\n"
      "      out = 4'd0;\n"
      "    else if (sel == 2'b01)\n"
      "      out = 4'd1;\n"
      "    else if (sel == 2'b10)\n"
      "      out = 4'd2;\n"
      "    else\n"
      "      out = 4'd3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_NE(stmt->else_branch, nullptr);
}

TEST(QualifiedIfParsing, UniqueIfWithElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique if (a) x = 1;\n"
      "    else x = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

TEST(QualifiedIfParsing, Unique0IfNoElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique0 if (a) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
}

TEST(QualifiedIfParsing, UniqueIfElseIfElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique if (a == 0) x = 1;\n"
      "    else if (a == 1) x = 2;\n"
      "    else if (a == 2) x = 3;\n"
      "    else x = 4;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);

  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->else_branch->qualifier, CaseQualifier::kNone);
}

TEST(QualifiedIfParsing, UniqueIfElseIfChain) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "    else x = 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

TEST(QualifiedIfParsing, Unique0IfElseIfNoFinalElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique0 if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
}

TEST(QualifiedIfParsing, PriorityIfElseIfWithElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "    else x = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

TEST(QualifiedIfParsing, PriorityIfNoFinalElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->else_branch->else_branch, nullptr);
}

TEST(QualifiedIfParsing, Unique0IfWithElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique0 if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "    else x = 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);
  EXPECT_NE(stmt->else_branch->else_branch, nullptr);
}

TEST(QualifiedIfParsing, NestedQualifiedIfs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority if (a) begin\n"
      "      unique if (b) x = 1;\n"
      "      else x = 2;\n"
      "    end else begin\n"
      "      x = 3;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* outer = FirstInitialStmt(r);
  ASSERT_NE(outer, nullptr);
  EXPECT_EQ(outer->qualifier, CaseQualifier::kPriority);
  ASSERT_NE(outer->then_branch, nullptr);
  EXPECT_EQ(outer->then_branch->kind, StmtKind::kBlock);
  auto* inner = outer->then_branch->stmts[0];
  ASSERT_NE(inner, nullptr);
  EXPECT_EQ(inner->qualifier, CaseQualifier::kUnique);
}

}  // namespace
