#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "lexer/token.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

// §16.13.7 by way of §16.10: the local variables a named property declares
// ahead of its body, `logic v = e;`, are captured with their type keyword
// and initialization assignment beside the body's tree.
TEST(PropertyLocalParsing, ALocalDeclaredAheadOfThePropertyIsCaptured) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    logic v = e;\n"
      "    (@(posedge clk1) (a == v)[*1:$] |-> b)\n"
      "    and\n"
      "    (@(posedge clk2) c[*1:$] |-> d == v);\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->prop_body_tree, nullptr);
  EXPECT_EQ(item->prop_body_tree->kind, PropertyExprNode::Kind::kAnd);
  ASSERT_EQ(item->prop_locals.size(), 1u);
  EXPECT_EQ(item->prop_locals[0].name, "v");
  EXPECT_EQ(item->prop_locals[0].type_kw, TokenKind::kKwLogic);
  ASSERT_NE(item->prop_locals[0].init, nullptr);
  EXPECT_EQ(item->prop_locals[0].init->text, "e");
}

// §16.10 with §7.4.1: a property's local declared of a packed type, `logic
// [3:0] x`, is captured with the packed dimension written after its keyword
// (#5745).
TEST(PropertyLocalParsing, APackedLocalIsCapturedWithItsDimension) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    logic [3:0] x;\n"
      "    @(posedge clk) (1, x = v + 12) |-> ##1 (x < 12);\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->prop_body_tree, nullptr);
  ASSERT_EQ(item->prop_locals.size(), 1u);
  ASSERT_EQ(item->prop_locals[0].packed_dims.size(), 1u);
  EXPECT_EQ(item->prop_locals[0].packed_dims[0].first->text, "3");
  EXPECT_EQ(item->prop_locals[0].packed_dims[0].second->text, "0");
}

// §16.10: a local declared without an initialization is captured with
// none, and a body without locals has none.
TEST(PropertyLocalParsing, ALocalWithoutAnInitializationHasNone) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    int x, y = 2;\n"
      "    @(posedge clk) a |-> ##1 c == x;\n"
      "  endproperty\n"
      "  property q;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_locals.size(), 2u);
  EXPECT_EQ(item->prop_locals[0].name, "x");
  EXPECT_EQ(item->prop_locals[0].init, nullptr);
  EXPECT_EQ(item->prop_locals[1].name, "y");
  ASSERT_NE(item->prop_locals[1].init, nullptr);
  const ModuleItem* q = nullptr;
  for (const auto* i : r.cu->modules[0]->items) {
    if (i->kind == ModuleItemKind::kPropertyDecl && i->name == "q") q = i;
  }
  ASSERT_NE(q, nullptr);
  EXPECT_TRUE(q->prop_locals.empty());
}

}  // namespace
