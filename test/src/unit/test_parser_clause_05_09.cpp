#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- §5.9: string literal in primary expression ---

TEST(ParserClause05, Cl5_9_PrimaryStringLiteral) {
  auto r = Parse("module m; initial x = \"hello\"; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStringLiteral);
}

TEST(ParserClause05, Cl5_9_ConstantPrimaryStringLiteral) {
  auto r = Parse("module m; parameter string S = \"hello\"; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kStringLiteral);
}

// --- §5.9: string literal in system call ---

TEST(ParserClause05, Cl5_9_StringInSystemCall) {
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"hello world\");\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  ASSERT_GE(stmt->expr->args.size(), 1u);
  EXPECT_EQ(stmt->expr->args[0]->kind, ExprKind::kStringLiteral);
}

// --- §5.9: string literal assignment ---

TEST(ParserClause05, Cl5_9_StringAssignment) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  byte c1;\n"
              "  initial c1 = \"A\";\n"
              "endmodule"));
}

TEST(ParserClause05, Cl5_9_StringPackedArray) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  bit [8*12:1] stringvar = \"Hello world\\n\";\n"
              "endmodule"));
}

// --- §5.9: string in concatenation ---

TEST(ParserClause05, Cl5_9_StringInConcatenation) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display({\"A\", \"B\"});\n"
              "endmodule"));
}

// --- §5.9: string literal with escaped content ---

TEST(ParserClause05, Cl5_9_StringWithWorld) {
  auto r = Parse("module m; initial x = \"world\"; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStringLiteral);
}

}  // namespace
