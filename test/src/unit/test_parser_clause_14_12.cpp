#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DefaultClockingParse, InlineWithNegedge) {
  auto r = Parse(
      "module m;\n"
      "  default clocking cb @(negedge clk);\n"
      "    input data;\n"
      "    output ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNegedge);
  ASSERT_EQ(item->clocking_signals.size(), 2u);
}

TEST(DefaultClockingParse, EndLabel) {
  auto r = Parse(
      "module m;\n"
      "  default clocking bus @(posedge clk);\n"
      "    input data;\n"
      "  endclocking : bus\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_EQ(item->name, "bus");
}

TEST(DefaultClockingParse, UnnamedWithMultipleSignals) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk);\n"
      "    input a, b;\n"
      "    output c;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_TRUE(item->name.empty());
  ASSERT_EQ(item->clocking_signals.size(), 3u);
}

TEST(DefaultClockingParse, ReferenceForm) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  default clocking cb;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  bool found_ref = false;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_default_clocking && item->clocking_event.empty()) {
      EXPECT_EQ(item->name, "cb");
      found_ref = true;
    }
  }
  EXPECT_TRUE(found_ref);
}

TEST(DefaultClockingParse, AsModuleItem) {
  auto r = Parse(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kClockingBlock);
  EXPECT_TRUE(r.cu->modules[0]->items[0]->is_default_clocking);
}

TEST(DefaultClockingParse, InlineInoutDirection) {
  auto r = Parse(
      "module t;\n"
      "  default clocking bus @(posedge clk);\n"
      "    inout data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_EQ(item->name, "bus");
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInout);
}

TEST(DefaultClockingParse, UnnamedInline) {
  auto r = Parse(
      "module t;\n"
      "  default clocking @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_TRUE(item->name.empty());
}

TEST(DefaultClockingParse, SeparateReferenceStatement) {
  auto r = Parse(
      "module t;\n"
      "  clocking busA @(posedge clk1);\n"
      "    input data;\n"
      "  endclocking\n"
      "  default clocking busA;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  bool found_ref = false;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_default_clocking && item->clocking_event.empty()) {
      EXPECT_EQ(item->name, "busA");
      found_ref = true;
    }
  }
  EXPECT_TRUE(found_ref);
}

TEST(DefaultClockingParse, NamedWithIsDefaultAndNotGlobal) {
  auto r = Parse(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_FALSE(item->is_global_clocking);
  EXPECT_EQ(item->name, "cb");
}

TEST(DefaultClockingParse, InInterface) {
  EXPECT_TRUE(
      ParseOk("interface my_if (input clk);\n"
              "  logic [7:0] data;\n"
              "  default clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endinterface\n"));
}

TEST(DefaultClockingParse, InProgram) {
  EXPECT_TRUE(
      ParseOk("program test(input logic clk);\n"
              "  default clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endprogram\n"));
}

TEST(DefaultClockingParse, DuplicateDefaultClockingParses) {
  auto r = Parse(
      "module m;\n"
      "  default clocking cb1 @(posedge clk1);\n"
      "    input a;\n"
      "  endclocking\n"
      "  default clocking cb2 @(posedge clk2);\n"
      "    input b;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  // Parser should accept it; elaborator rejects duplicates.
  auto& items = r.cu->modules[0]->items;
  size_t default_count = 0;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_default_clocking)
      ++default_count;
  }
  EXPECT_EQ(default_count, 2u);
}

}  // namespace
