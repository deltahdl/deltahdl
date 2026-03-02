// §16.12.4: Disjunction property

#include "fixture_parser.h"

using namespace delta;

namespace {

// property_expr ::= property_expr or property_expr
TEST(ParserA210, PropertyExpr_Or) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a or b);\n"
              "endmodule\n"));
}

using VerifyParseTest = ProgramTestParse;

// Assert property with or (disjunction).
TEST(ParserSection16, Sec16_5_1_PropertyOr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) (a |-> b) or (c |-> d));\n"
              "endmodule\n"));
}

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

// --- F.12: Property or ---
TEST(ParserAnnexF, AnnexFPropertyOr) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (a |-> b) or (c |-> d));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

}  // namespace
