#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "lexer/token.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

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

// §16.10 with §6.11: a property's locals are captured with the signing
// keyword written after their type keyword, and with none where none is.
TEST(PropertyLocalParsing, ALocalsSigningKeywordIsCaptured) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    logic signed [3:0] s; int unsigned u; bit b;\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_locals.size(), 3u);
  EXPECT_EQ(item->prop_locals[0].signing, TokenKind::kKwSigned);
  EXPECT_EQ(item->prop_locals[1].signing, TokenKind::kKwUnsigned);
  EXPECT_EQ(item->prop_locals[2].signing, TokenKind::kEof);
}

// §16.10 with §6.18: a property's local declared with a type name the module
// declares is captured with that name in its keyword's place, and with the
// packed dimensions written after the name.
TEST(PropertyLocalParsing, ALocalOfATypeNameIsCaptured) {
  auto r = Parse(
      "module m;\n"
      "  typedef logic [3:0] nib_t;\n"
      "  property p;\n"
      "    nib_t v;\n"
      "    nib_t [1:0] w;\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->prop_body_tree, nullptr);
  ASSERT_EQ(item->prop_locals.size(), 2u);
  EXPECT_EQ(item->prop_locals[0].named_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(item->prop_locals[0].named_type.type_name, "nib_t");
  EXPECT_TRUE(item->prop_locals[0].packed_dims.empty());
  EXPECT_EQ(item->prop_locals[1].packed_dims.size(), 1u);
}

// §16.10 with §6.24.1: a property whose body opens with a cast to a type
// name, `nib_t'(a)`, declares no local.
TEST(PropertyLocalParsing, ACastToATypeNameDeclaresNoLocal) {
  auto r = Parse(
      "module m;\n"
      "  typedef logic [3:0] nib_t;\n"
      "  property p;\n"
      "    nib_t'(a) == 4'd1;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->prop_locals.empty());
}

// §16.10: a sequence whose local declaration is malformed, `int ;`, naming
// no variable, has no operands captured.
TEST(PropertyLocalParsing, AMalformedSequenceLocalLeavesTheBodyUncaptured) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    int ;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->seq_linear.operands.empty());
}

// §16.10: a property whose local declaration is malformed, `int ;`, naming
// no variable, has no body captured.
TEST(PropertyLocalParsing, AMalformedLocalLeavesTheBodyUncaptured) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    int ;\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->prop_body_tree, nullptr);
  EXPECT_TRUE(item->prop_locals.empty());
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
