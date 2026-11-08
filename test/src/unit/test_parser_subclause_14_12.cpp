#include <gtest/gtest.h>

#include <string_view>
#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

ModuleItem* FindClockingNamed(const std::vector<ModuleItem*>& items,
                              std::string_view name) {
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kClockingBlock && it->name == name)
      return it;
  }
  return nullptr;
}

TEST(DefaultClockingParse, AssignmentFormInModuleIsDefaultWithoutEvent) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  logic a;\n"
      "  clocking cb @(posedge clk);\n"
      "    input a;\n"
      "  endclocking\n"
      "  default clocking cb;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* assign = FindClockingBlockByIndex(r, 1);
  ASSERT_NE(assign, nullptr);
  EXPECT_TRUE(assign->is_default_clocking);
  EXPECT_EQ(assign->name, "cb");
  EXPECT_TRUE(assign->clocking_event.empty());
  EXPECT_TRUE(assign->clocking_signals.empty());
}

TEST(DefaultClockingParse, InlineFormInModuleIsDefaultWithEvent) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  logic a;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input a;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_EQ(item->name, "cb");
  EXPECT_FALSE(item->clocking_event.empty());
}

TEST(DefaultClockingParse, PlainClockingIsNotDefault) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  logic a;\n"
      "  clocking cb @(posedge clk);\n"
      "    input a;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  EXPECT_FALSE(item->is_default_clocking);
  EXPECT_FALSE(item->clocking_event.empty());
}

TEST(DefaultClockingParse, AssignmentFormInChecker) {
  auto r = Parse(
      "checker c(input logic clk, input logic a);\n"
      "  clocking cb @(posedge clk);\n"
      "    input a;\n"
      "  endclocking\n"
      "  default clocking cb;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->checkers.empty());
  const auto& items = r.cu->checkers[0]->items;
  auto* assign = FindClockingNamed(items, "cb");
  ModuleItem* default_assign = nullptr;
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kClockingBlock && it->is_default_clocking &&
        it->clocking_event.empty()) {
      default_assign = it;
    }
  }
  ASSERT_NE(assign, nullptr);
  ASSERT_NE(default_assign, nullptr);
  EXPECT_EQ(default_assign->name, "cb");
}

TEST(DefaultClockingParse, InlineDefaultInInterface) {
  auto r = Parse(
      "interface intf(input clk, input a);\n"
      "  default clocking cb @(posedge clk);\n"
      "    input a;\n"
      "  endclocking\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->interfaces.empty());
  auto* item = FindClockingNamed(r.cu->interfaces[0]->items, "cb");
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_default_clocking);
}

TEST(DefaultClockingParse, InlineDefaultInProgram) {
  auto r = Parse(
      "program p(input clk, input a);\n"
      "  default clocking cb @(posedge clk);\n"
      "    input a;\n"
      "  endclocking\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->programs.empty());
  auto* item = FindClockingNamed(r.cu->programs[0]->items, "cb");
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_default_clocking);
}

TEST(DefaultClockingParse, InlineDefaultInChecker) {
  auto r = Parse(
      "checker c(input logic clk, input logic a);\n"
      "  default clocking cb @(posedge clk);\n"
      "    input a;\n"
      "  endclocking\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->checkers.empty());
  auto* item = FindClockingNamed(r.cu->checkers[0]->items, "cb");
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_FALSE(item->clocking_event.empty());
}

TEST(DefaultClockingParse, MissingIdentifierRejected) {
  auto r = Parse(
      "module m;\n"
      "  default clocking ;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected '@', got ';'", 2, "14.3"));
}

}  // namespace
