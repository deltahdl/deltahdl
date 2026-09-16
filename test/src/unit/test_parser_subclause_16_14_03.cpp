#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(AssertionSemanticsParsing, CoverProperty) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kCoverProperty) {
      found = true;
      EXPECT_NE(item->assert_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

// §16.14.3 and §16.12.1: a cover statement whose whole spec is one name is an
// instance of a named property or sequence when the name is a declaration's.
// The parser records the name for the elaborator to substitute the body, as
// it does for an assert, and reports nothing, so the cover is not left
// unevaluated at the parse for opening with no clocking event.
TEST(AssertionSemanticsParsing, CoverInstanceSpecIsRecordedUnreported) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    @(posedge clk) a |=> b;\n"
      "  endproperty\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  cp: cover property (p) x++;\n"
      "  cs: cover sequence (s);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.diags.empty());
  ASSERT_EQ(r.cu->modules.size(), 1u);
  const ModuleItem* cp = nullptr;
  const ModuleItem* cs = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kCoverProperty) cp = item;
    if (item->kind == ModuleItemKind::kCoverSequence) cs = item;
  }
  ASSERT_NE(cp, nullptr);
  EXPECT_EQ(cp->prop_instance_name, "p");
  EXPECT_EQ(cp->body, nullptr);
  EXPECT_NE(cp->assert_pass_stmt, nullptr);
  ASSERT_NE(cs, nullptr);
  EXPECT_EQ(cs->prop_instance_name, "s");
  EXPECT_EQ(cs->body, nullptr);
}

}  // namespace
