#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection19, GlobalClocking_Basic) {
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

TEST(ParserSection19, GlobalClocking_CompoundEvent) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  global clocking sys @(clk1 or clk2);\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ParserSection19, GlobalClocking_EndLabel) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  global clocking gclk @(posedge clk);\n"
              "  endclocking : gclk\n"
              "endmodule\n"));
}

TEST(ParserSection14, GlobalClockingEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  global clocking gclk @(posedge sys_clk);\n"
      "  endclocking : gclk\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_EQ(item->name, "gclk");
}

TEST(ParserSection14, GlobalClockingNoSignals) {
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

TEST(ParserSection14, GlobalClockingSubsystemPattern) {
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

TEST(ParserA611, GlobalClockingUnnamed) {
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

TEST(ParserA611, GlobalClockingCompoundEvent) {
  auto r = Parse(
      "module m;\n"
      "  global clocking sys @(clk1 or clk2); endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_GE(item->clocking_event.size(), 2u);
}

TEST(ParserA611, ClockingDeclGlobal) {
  auto r = Parse(
      "module m;\n"
      "  global clocking gclk @(posedge sys_clk);\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_FALSE(item->is_default_clocking);
  EXPECT_EQ(item->name, "gclk");
  EXPECT_TRUE(item->clocking_signals.empty());
}

TEST(ParserSection14, GlobalClocking) {
  auto r = Parse(
      "module m;\n"
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

}  // namespace
