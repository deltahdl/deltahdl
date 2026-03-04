// §5.6.3: System tasks and system functions

#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"
#include "simulator/vpi.h"

using namespace delta;

namespace {

// system_tf_call with empty parentheses
TEST(ParserA609, SystemTfCallEmptyParens) {
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

// system_tf_call with arguments
TEST(ParserA609, SystemTfCallWithArgs) {
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

// system_tf_call with empty positional arguments (commas with no expressions)
TEST(ParserA609, SystemTfCallEmptyArgs) {
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

// =============================================================================
// LRM section 38.36 -- vpi_register_cb: DPI-C imports for VPI callbacks
// These tests verify that DPI-C import declarations with signatures typical
// of VPI callback routines parse correctly.
// =============================================================================
TEST(ParserSection38, VpiSystemCallDeposit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $deposit(sig, 1'b1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =========================================================================
// Section 5.6.3: System tasks and system functions
// =========================================================================
TEST(ParserCh50603, SystemTask_Display) {
  // $display is a system task call (Section 5.6.3, Section 21.2).
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

}  // namespace
