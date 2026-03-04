// §16.14.5: Using concurrent assertion statements outside procedural code

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA210, ConcurrentAssertionItem_AssumeProperty) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req |-> ack);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(item, nullptr);
}

// =============================================================================
// Additional AST verification tests
// =============================================================================
TEST(ParserA210, AllFiveConcurrentAssertionTypes) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a |-> b);\n"
      "  assume property (c |-> d);\n"
      "  cover property (e ##1 f);\n"
      "  cover sequence (g ##1 h);\n"
      "  restrict property (i |-> j);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty),
      nullptr);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty),
      nullptr);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty),
      nullptr);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverSequence),
      nullptr);
  ASSERT_NE(FindItemByKind(r.cu->modules[0]->items,
                           ModuleItemKind::kRestrictProperty),
            nullptr);
}

// --- Test helpers ---
// =============================================================================
// Combination: property used with assert
// =============================================================================
TEST(ParserSection16, PropertyDeclAndAssertProperty) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "  assert property (p1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found_prop = false;
  bool found_assert = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl) found_prop = true;
    if (item->kind == ModuleItemKind::kAssertProperty) found_assert = true;
  }
  EXPECT_TRUE(found_prop);
  EXPECT_TRUE(found_assert);
}

}  // namespace
