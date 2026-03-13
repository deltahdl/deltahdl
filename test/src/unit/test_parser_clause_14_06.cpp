#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(SignalMultiBlockParse, SameSignalInTwoBlocks) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb1 @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  clocking cb2 @(negedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules.size(), 1u);
  auto& items = r.cu->modules[0]->items;
  int clocking_count = 0;
  for (const auto* item : items) {
    if (item->kind == ModuleItemKind::kClockingBlock) ++clocking_count;
  }
  EXPECT_EQ(clocking_count, 2);
}

TEST(SignalMultiBlockParse, SameSignalInputAndOutput) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb1 @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  clocking cb2 @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SignalMultiBlockParse, SharedClockSignal) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb1 @(posedge clk);\n"
      "    input a;\n"
      "  endclocking\n"
      "  clocking cb2 @(posedge clk);\n"
      "    input b;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
