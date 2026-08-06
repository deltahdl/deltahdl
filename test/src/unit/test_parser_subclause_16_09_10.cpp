#include "fixture_parser.h"

using namespace delta;

namespace {

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

TEST(AssertionSemanticsParsing, Within) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (a ##[1:3] b) within (c ##[1:5] d));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.9.10: `within`'s desugaring `(1[*0:$] ##1 seq1 ##1 1[*0:$]) intersect
// seq2` is built on a `[*0:$]` repetition (§16.9.2), and the standard's own
// example — `!trdy[*7] within ($fell(irdy) ##1 !irdy[*8])` — contains a
// `within` whose operands are themselves repetitions. The parser must accept a
// `within` whose contained and containing operands are §16.9.2 repetition
// sequences.
TEST(AssertionSemanticsParsing, WithinContainsRepeatedSequence) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (!trdy)[*7] within (start_irdy ##1 (!irdy)[*8]));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.9.10: the containing operand may itself be an `intersect` composition —
// the very operator (§16.9.6) that the `within` desugaring is defined in terms
// of. The parser must accept a `within` whose right operand is an intersect of
// two sequences.
TEST(AssertionSemanticsParsing, WithinContainsIntersectSequence) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (a ##1 b) within ((c ##1 d) intersect (e ##2 f)));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

}  // namespace
