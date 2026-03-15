#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SystemNameParsing, SystemTaskDisplay) {
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"hello\");\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
}

TEST(SystemNameParsing, SystemTfCallEmptyParens) {
  auto r = Parse(
      "module m;\n"
      "  initial $finish();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(expr->callee, "$finish");
  EXPECT_TRUE(expr->args.empty());
}

TEST(SystemNameParsing, SystemTfCallWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial $display(\"x=%0d\", x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(expr->callee, "$display");
  EXPECT_EQ(expr->args.size(), 2u);
}

TEST(SystemNameParsing, SystemTfCallEmptyArgs) {
  auto r = Parse(
      "module m;\n"
      "  initial $display(,,1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(expr->args.size(), 3u);
  EXPECT_EQ(expr->args[0], nullptr);
  EXPECT_EQ(expr->args[1], nullptr);
  ASSERT_NE(expr->args[2], nullptr);
}

TEST(SystemNameParsing, SystemDeposit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $deposit(sig, 1'b1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SystemNameParsing, SystemFunctionInExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $time;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SystemNameParsing, SystemTaskNoParens) {
  auto r = Parse(
      "module m;\n"
      "  initial $finish;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(expr->callee, "$finish");
}

TEST(SystemNameParsing, SystemFunctionInAssign) {
  auto r = Parse(
      "module m;\n"
      "  logic [31:0] w;\n"
      "  assign w = $clog2(16);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SystemNameParsing, SystemFunctionWithDataTypeArg) {
  auto r = Parse(
      "module m;\n"
      "  logic [31:0] w;\n"
      "  assign w = $bits(logic [7:0]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SystemNameParsing, SystemTaskInTaskBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task t;\n"
              "    $display(\"in task\");\n"
              "  endtask\n"
              "endmodule\n"));
}

TEST(SystemNameParsing, SystemTaskInFunctionBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void f;\n"
              "    $display(\"in func\");\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(SystemNameParsing, EmbeddedDollarSystemCallParses) {
  auto r = Parse(
      "module m;\n"
      "  initial $test$plusargs(\"flag\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(expr->callee, "$test$plusargs");
}

}  // namespace
