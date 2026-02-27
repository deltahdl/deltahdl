// Annex A.2.10: Assertion declarations

#include "fixture_parser.h"

using namespace delta;

static ModuleItem* FindItemByKind(const std::vector<ModuleItem*>& items,
                                  ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

namespace {

// property_expr ::= ( property_expr )
TEST(ParserA210, PropertyExpr_Parenthesized) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) (a |-> b));\n"
              "endmodule\n"));
}

// property_expr ::= property_expr and property_expr
TEST(ParserA210, PropertyExpr_And) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a and b);\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyAndSequenceDeclsTogether) {
  auto r = Parse(
      "module m;\n"
      "  property p; a; endproperty\n"
      "  sequence s; b; endsequence\n"
      "  assert property (p);\n"
      "  cover sequence (s);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kPropertyDecl),
      nullptr);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kSequenceDecl),
      nullptr);
}

// sequence_actual_arg ::= event_expression
TEST(ParserA210, SequenceActualArg_EventExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b); a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s(posedge x, y));\n"
              "endmodule\n"));
}

}  // namespace
