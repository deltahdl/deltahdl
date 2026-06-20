#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ClockingBlockEventParse, AlwaysAtBlockName) {
  auto r = Parse(
      "module foo(input phi1, input [7:0] data);\n"
      "  clocking dram @(posedge phi1);\n"
      "    input data;\n"
      "  endclocking\n"
      "  always @(dram)\n"
      "    $display(\"triggered\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "dram");
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(ClockingBlockEventParse, PosedgeAndBlockEventCoexist) {
  auto r = Parse(
      "module m;\n"
      "  clocking dram @(posedge phi1);\n"
      "    input data;\n"
      "  endclocking\n"
      "  always @(posedge phi1) $display(\"clock\");\n"
      "  always @(dram) $display(\"block event\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_GE(r.cu->modules[0]->items.size(), 3u);
}

TEST(ClockingBlockEventParse, BlockEventWithMultipleSignals) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input a, b, c;\n"
      "  endclocking\n"
      "  always @(cb) $display(\"triggered\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 3u);
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(ClockingBlockEventParse, InitialBlockWaitsOnBlockEvent) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking cb @(posedge clk);\n"
              "    input v;\n"
              "  endclocking\n"
              "  initial begin\n"
              "    @(cb);\n"
              "    $display(cb.v);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ClockingBlockEventParse, OutputNegedgeWithBlockEvent) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking dram @(posedge phi1);\n"
              "    input data;\n"
              "    output negedge #1 address;\n"
              "  endclocking\n"
              "  always @(posedge phi1) $display(\"clock\");\n"
              "  always @(dram) $display(\"block event\");\n"
              "endmodule\n"));
}

}  // namespace
