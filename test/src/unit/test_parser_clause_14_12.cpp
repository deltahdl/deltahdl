#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Locate a clocking-block item by name within an item list (used for checker,
// interface, and program bodies, which do not live under cu->modules).
ModuleItem* FindClockingNamed(const std::vector<ModuleItem*>& items,
                              std::string_view name) {
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kClockingBlock && it->name == name)
      return it;
  }
  return nullptr;
}

// §14.12 / Syntax 14-3 (A.1.4): the assignment form
//   module_or_generate_item_declaration ::= ... | default clocking
//   clocking_identifier ;
// names an existing clocking block as the default. The parser records it as a
// clocking-block item flagged default and carrying no clocking event (the empty
// event is exactly what distinguishes this form from the inline declaration and
// is what the elaborator keys on to resolve the referenced block).
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
  // Two clocking-block items: the inline declaration and the
  // default-assignment.
  auto* assign = FindClockingBlockByIndex(r, 1);
  ASSERT_NE(assign, nullptr);
  EXPECT_TRUE(assign->is_default_clocking);
  EXPECT_EQ(assign->name, "cb");
  EXPECT_TRUE(assign->clocking_event.empty());
  EXPECT_TRUE(assign->clocking_signals.empty());
}

// §14.12 / Syntax 14-3 (A.6.11): the inline form carries the optional `default`
// qualifier on a full clocking_declaration
//   clocking_declaration ::= [ default ] clocking [ clocking_identifier ]
//   clocking_event ; ...
// The parser flags the block default and keeps its clocking event (Example 1).
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

// §14.12: the `default` qualifier of Syntax 14-3 is what marks a block as the
// default. Absent it, an otherwise identical clocking_declaration is an
// ordinary (non-default) clocking block, confirming the `[ default ]` option
// drives the flag rather than the surrounding syntax.
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

// §14.12 / Syntax 14-3 (A.1.8): the assignment form is equally a
//   checker_or_generate_item_declaration ::= ... | default clocking
//   clocking_identifier ;
// so a checker body admits the same `default clocking <id>;` statement.
TEST(DefaultClockingParse, AssignmentFormInChecker) {
  auto r = Parse(
      "checker c(input clk, input a);\n"
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
  // The last matching item is the assignment form: locate the default one with
  // no event.
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

// §14.12: a default clocking may be specified in an interface. The inline form
// is accepted there and flagged default.
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

// §14.12: a default clocking may equally be specified in a program.
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

// §14.12: a checker is one of the scopes that may carry a default clocking, and
// the inline `[ default ] clocking ...` form (A.6.11) is admitted there just as
// the assignment form is. This covers the inline-default syntactic position in
// a checker (complementing AssignmentFormInChecker's assignment position).
TEST(DefaultClockingParse, InlineDefaultInChecker) {
  auto r = Parse(
      "checker c(input clk, input a);\n"
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

// §14.12 (negative): the assignment form requires a clocking_identifier. A
// `default clocking ;` with neither a name nor a clocking event matches no
// production of Syntax 14-3 and shall be rejected.
TEST(DefaultClockingParse, MissingIdentifierRejected) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  default clocking ;\n"
              "endmodule\n"));
}

}  // namespace
