#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(CheckerBuildingBlock, CheckerEndcheckerEnclosesTheBlock) {
  auto r = Parse(
      "checker req_gnt;\n"
      "endchecker : req_gnt\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "req_gnt");
  EXPECT_EQ(r.cu->checkers[0]->decl_kind, ModuleDeclKind::kChecker);
}

TEST(CheckerBuildingBlock, CheckerHoldsAssertionsBesideModelingCode) {
  auto r = Parse(
      "checker req_gnt(logic clk, logic req, logic gnt);\n"
      "  logic seen = 1'b0;\n"
      "  always_ff @(posedge clk) seen <= seen | req;\n"
      "  a_gnt: assert property (@(posedge clk) gnt |-> seen);\n"
      "  c_req: cover property (@(posedge clk) req);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  const auto& items = r.cu->checkers[0]->items;
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kVarDecl));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kAlwaysFFBlock));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kAssertProperty));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kCoverProperty));
}

}  // namespace
