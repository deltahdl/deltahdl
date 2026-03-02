// §16.9.8: First_match operation

#include "fixture_parser.h"

using namespace delta;

namespace {

// sequence_expr ::= first_match ( sequence_expr {, sequence_match_item} )
TEST(ParserA210, SequenceExpr_FirstMatch) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    first_match(a ##[1:5] b));\n"
              "endmodule\n"));
}

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

// --- F.6: first_match ---
TEST(ParserAnnexF, AnnexFFirstMatch) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) first_match(a ##[1:4] b));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

}  // namespace
