#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ClockingHierExprParse, SimpleHierarchicalExpression) {
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

TEST(ClockingHierExprParse, MixedSignalsWithAndWithoutHierExpr) {
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

TEST(ClockingHierExprParse, ConcatenationExpression) {
  auto r = Parse(
      "module m;\n"
      "  clocking mem @(clock);\n"
      "    input instruction = { opcode, regA, regB[3:1] };\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "instruction");
  EXPECT_NE(item->clocking_signals[0].hier_expr, nullptr);
}

TEST(ClockingHierExprParse, PartSelectExpression) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input nibble = data[7:4];\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "nibble");
  EXPECT_NE(item->clocking_signals[0].hier_expr, nullptr);
}

}  // namespace
