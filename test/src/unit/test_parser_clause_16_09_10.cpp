// §16.9.10: Sequence contained within another sequence

#include "fixture_parser.h"

using namespace delta;

namespace {

// sequence_expr ::= sequence_expr within sequence_expr
TEST(ParserA210, SequenceExpr_Within) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b) within (c ##[1:5] d));\n"
              "endmodule\n"));
}

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

// --- F.8: within ---
TEST(ParserAnnexF, AnnexFWithin) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (a ##[1:3] b) within (c ##[1:5] d));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

}  // namespace
