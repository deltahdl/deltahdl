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

// §14.6 names inouts among the signal directions that may recur across
// clocking blocks. The parser accepts the same inout signal in two blocks.
TEST(SignalMultiBlockParse, InoutSignalInTwoBlocks) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb1 @(posedge clk);\n"
      "    inout data;\n"
      "  endclocking\n"
      "  clocking cb2 @(negedge clk);\n"
      "    inout data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules.size(), 1u);
  int clocking_count = 0;
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kClockingBlock) ++clocking_count;
  }
  EXPECT_EQ(clocking_count, 2);
}

// §14.6 also lists outputs among the signal directions that may recur across
// clocking blocks. The parser accepts the same output signal declared in two
// blocks without flagging the reuse.
TEST(SignalMultiBlockParse, SameOutputSignalInTwoBlocks) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb1 @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  clocking cb2 @(negedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules.size(), 1u);
  int clocking_count = 0;
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kClockingBlock) ++clocking_count;
  }
  EXPECT_EQ(clocking_count, 2);
}

}
