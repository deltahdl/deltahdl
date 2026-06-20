#include "fixture_parser.h"

using namespace delta;

namespace {

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

// §16.12.6: the two-branch form `if (expr) p1 else p2`.
TEST(AssertionSemanticsParsing, PropertyIfElse) {
  auto r = Parse(
      "module m;\n"
      "  property p_cond;\n"
      "    @(posedge clk) if (mode) a |-> b; else c |-> d;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kPropertyDecl));
}

// §16.12.6: the single-branch form `if (expr) p` with no else is equally a
// valid if-else property and must be accepted on its own.
TEST(AssertionSemanticsParsing, PropertyIfWithoutElse) {
  auto r = Parse(
      "module m;\n"
      "  property p_cond;\n"
      "    @(posedge clk) if (mode) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kPropertyDecl));
}

// §16.12.6 edge case: the else-branch property_expr of the two-branch form may
// itself be another if-else, so an if/else-if/else chain is still one valid
// if-else property declaration.
TEST(AssertionSemanticsParsing, PropertyIfElseIfChain) {
  auto r = Parse(
      "module m;\n"
      "  property p_cond;\n"
      "    @(posedge clk) if (s == 0) a |-> b;\n"
      "    else if (s == 1) c |-> d;\n"
      "    else e |-> f;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kPropertyDecl));
}

}  // namespace
