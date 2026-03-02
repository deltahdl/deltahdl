// §16.9.6: Intersection (AND with length restriction)

#include "fixture_parser.h"

using namespace delta;

namespace {

// sequence_expr ::= sequence_expr intersect sequence_expr
TEST(ParserA210, SequenceExpr_Intersect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b) intersect (c ##1 d));\n"
              "endmodule\n"));
}

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

// --- F.9: intersect ---
TEST(ParserAnnexF, AnnexFIntersect) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (a ##[1:5] b) intersect (c ##[2:4] d));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

}  // namespace
