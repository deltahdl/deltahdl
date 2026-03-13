#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(GlobalClockingParse, BasicNamedPosedge) {
  auto r = Parse(
      "module t;\n"
      "  global clocking gclk @(posedge sys_clk);\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_EQ(item->name, "gclk");
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_FALSE(item->is_default_clocking);
  EXPECT_TRUE(item->clocking_signals.empty());
}

TEST(GlobalClockingParse, CompoundOrEvent) {
  auto r = Parse(
      "module t;\n"
      "  global clocking sys @(clk1 or clk2);\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_GE(item->clocking_event.size(), 2u);
}

TEST(GlobalClockingParse, EndLabel) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  global clocking gclk @(posedge clk);\n"
              "  endclocking : gclk\n"
              "endmodule\n"));
}

TEST(GlobalClockingParse, NoSignalsAllowed) {
  auto r = Parse(
      "module m;\n"
      "  global clocking gc @(negedge clk); endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_TRUE(item->clocking_signals.empty());
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNegedge);
}

TEST(GlobalClockingParse, SubsystemPattern) {
  auto r = Parse(
      "module subsystem1;\n"
      "  logic subclk1;\n"
      "  global clocking sub_sys1 @(subclk1); endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_EQ(item->name, "sub_sys1");
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNone);
}

TEST(GlobalClockingParse, UnnamedGlobalClocking) {
  auto r = Parse(
      "module m;\n"
      "  global clocking @(negedge clk); endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_TRUE(item->name.empty());
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNegedge);
}

TEST(GlobalClockingParse, InInterface) {
  EXPECT_TRUE(
      ParseOk("interface my_if (input clk);\n"
              "  global clocking gc @(posedge clk); endclocking\n"
              "endinterface\n"));
}

TEST(GlobalClockingParse, InProgram) {
  EXPECT_TRUE(
      ParseOk("program test(input logic clk);\n"
              "  global clocking gc @(posedge clk); endclocking\n"
              "endprogram\n"));
}

TEST(GlobalClockingParse, DuplicateGlobalClockingParses) {
  auto r = Parse(
      "module m;\n"
      "  global clocking gc1 @(posedge clk1); endclocking\n"
      "  global clocking gc2 @(posedge clk2); endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  // Parser accepts; elaborator rejects duplicates.
  auto& items = r.cu->modules[0]->items;
  size_t global_count = 0;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_global_clocking)
      ++global_count;
  }
  EXPECT_EQ(global_count, 2u);
}

TEST(GlobalClockingParse, GlobalClockSystemFunctionCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  global clocking gc @(posedge clk); endclocking\n"
              "  always @($global_clock) begin\n"
              "  end\n"
              "endmodule\n"));
}

TEST(GlobalClockingParse, NotDefaultNotGlobal) {
  auto r = Parse(
      "module m;\n"
      "  global clocking gclk @(posedge sys_clk);\n"
      "  endclocking\n"
      "endmodule\n");
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_FALSE(item->is_default_clocking);
}

}  // namespace
