#include "fixture_parser.h"

using namespace delta;

namespace {

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

// §16.9.7 Syntax 16-9: `sequence_expr ::= sequence_expr or sequence_expr`. The
// `or` of two sequence operands is accepted in the property spec of an
// assertion.
TEST(AssertionSemanticsParsing, Or) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (a ##2 b) or (c ##2 d ##2 e));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.9.7: the operands of `or` may be plain Boolean expressions rather than
// multi-tick sequences. The same sequence_expr production accepts that
// expression-operand form, so it too parses into an assertion item.
TEST(AssertionSemanticsParsing, OrOfBooleanExpressions) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a or b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.9.7: the `or` of two sequences is a sequence_expr, so it is accepted in
// every position that admits one. A cover-property spec is a distinct syntactic
// position (parsed by a separate item path from an assert), so the operator is
// exercised there too.
TEST(AssertionSemanticsParsing, OrInCoverProperty) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) (a ##2 b) or (c ##2 d ##2 e));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kCoverProperty));
}

// §16.9.7: a named sequence declaration is another syntactic position for the
// `or` operator — its body is a sequence_expr. The declaration parses as a
// sequence item with the operator in its body.
TEST(AssertionSemanticsParsing, OrInSequenceDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    (a ##2 b) or (c ##2 d ##2 e);\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kSequenceDecl));
}

}  // namespace
