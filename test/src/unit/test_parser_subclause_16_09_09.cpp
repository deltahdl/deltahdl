#include "fixture_parser.h"

using namespace delta;

namespace {

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

TEST(AssertionSemanticsParsing, Throughout) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) enable throughout (a ##1 b ##1 c));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.9.9: the left operand of `throughout` is a condition and the right
// operand is a full sequence. The desugaring `(exp)[*0:$] intersect seq` leans
// on consecutive repetition (§16.9.2), so the guarded sequence must be allowed
// to carry a `[*N]` repetition. This mirrors the shape of the standard's own
// burst example: a negated condition held throughout a repeated match.
TEST(AssertionSemanticsParsing, ThroughoutGuardsRepeatedSequence) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge mclk)\n"
      "      (!burst_mode) throughout (##2 ((trdy==0)&&(irdy==0)) [*7]));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.9.9: the guarded sequence may itself be an intersect composition — the
// very operator (§16.9.6) the throughout desugaring is defined in terms of. The
// parser must accept a throughout whose right operand is an intersect of two
// subsequences.
TEST(AssertionSemanticsParsing, ThroughoutGuardsIntersectSequence) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) enable throughout ((a ##1 b) intersect (c ##1 d)));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

}  // namespace
