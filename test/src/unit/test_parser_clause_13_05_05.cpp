#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SubroutineCallSyntaxParsing, TaskCallWithoutParens) {
  auto r = Parse(
      "module m;\n"
      "  task foo; endtask\n"
      "  initial foo;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(SubroutineCallSyntaxParsing, VoidFunctionCallWithoutParens) {
  auto r = Parse(
      "module m;\n"
      "  function void do_it; endfunction\n"
      "  initial do_it;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->expr->text, "do_it");
}

TEST(SubroutineCallSyntaxParsing, TaskAllDefaultsWithoutParens) {
  auto r = Parse(
      "module m;\n"
      "  task do_it(int a = 1, int b = 2); endtask\n"
      "  initial do_it;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kIdentifier);
}

TEST(SubroutineCallSyntaxParsing, VoidFunctionAllDefaultsWithoutParens) {
  auto r = Parse(
      "module m;\n"
      "  function void do_it(int x = 5); endfunction\n"
      "  initial do_it;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kIdentifier);
}

// §13.5.5: A class function method without arguments may be called without
// the empty parentheses; the bare member access shall parse cleanly.
TEST(SubroutineCallSyntaxParsing, ClassMethodNoArgsWithoutParens) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  function void touch; endfunction\n"
              "endclass\n"
              "module m;\n"
              "  C c;\n"
              "  initial c.touch;\n"
              "endmodule\n"));
}

// §13.5.5: A class method whose arguments all have defaults may be called
// without the empty parentheses.
TEST(SubroutineCallSyntaxParsing, ClassMethodAllDefaultsWithoutParens) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  function void take(int v = 1); endfunction\n"
              "endclass\n"
              "module m;\n"
              "  C c;\n"
              "  initial c.take;\n"
              "endmodule\n"));
}

}  // namespace
