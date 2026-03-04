// §14.5: Hierarchical expressions

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.6.11 clocking_decl_assign — signal_identifier = expression
// =============================================================================
TEST(ParserA611, ClockingDeclAssignWithHierExpr) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input enable = top.dut.enable;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "enable");
  EXPECT_NE(item->clocking_signals[0].hier_expr, nullptr);
}

// =============================================================================
// A.6.11 clocking_decl_assign — multiple with mixed hier_expr
// =============================================================================
TEST(ParserA611, ClockingDeclAssignMultipleMixed) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input a, b = top.sig_b, c;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 3u);
  EXPECT_EQ(item->clocking_signals[0].hier_expr, nullptr);
  EXPECT_NE(item->clocking_signals[1].hier_expr, nullptr);
  EXPECT_EQ(item->clocking_signals[2].hier_expr, nullptr);
}
// Hierarchical expression assignment to a clocking signal.
TEST(ParserSection19, ClockingBlock_HierarchicalExpr) {
  auto r = Parse(
      "module t;\n"
      "  clocking cb @(posedge clk);\n"
      "    input enable = top.mem1.enable;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "enable");
  ASSERT_NE(item->clocking_signals[0].hier_expr, nullptr);
}
// =============================================================================
// §14.5 — Hierarchical expression assignment
// =============================================================================
TEST(ParserSection14, HierarchicalExpression) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input enable = top.mem1.enable;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "enable");
  ASSERT_NE(item->clocking_signals[0].hier_expr, nullptr);
}

}  // namespace
