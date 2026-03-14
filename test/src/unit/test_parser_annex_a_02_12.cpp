#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ConstraintDeclParsing, LetPortItem_ExplicitType) {
  auto r = Parse(
      "module m;\n"
      "  let f(logic [15:0] val) = val;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "val");
}

TEST(ConstraintDeclParsing, LetPortItem_WithDefault) {
  auto r = Parse(
      "module m;\n"
      "  let f(x = 42) = x;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "x");
  EXPECT_NE(item->func_args[0].default_value, nullptr);
}

TEST(ConstraintDeclParsing, LetPortItem_NoDefault) {
  auto r = Parse(
      "module m;\n"
      "  let f(x) = x;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->func_args[0].default_value, nullptr);
}

TEST(ConstraintDeclParsing, LetPortItem_WithUnpackedDim) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(logic x [3:0]) = x[0];\n"
              "endmodule\n"));
}

TEST(ConstraintDeclParsing, LetPortItem_TypedWithDefault) {
  auto r = Parse(
      "module m;\n"
      "  let at_least(logic sig, logic rst = 1'b0) = rst || sig;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].default_value, nullptr);
  EXPECT_NE(item->func_args[1].default_value, nullptr);
}

TEST(ConstraintDeclParsing, LetPortItem_IntType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(int a, int b) = a * b;\n"
              "endmodule\n"));
}

TEST(ConstraintDeclParsing, LetPortItem_BitType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(bit [7:0] x) = x;\n"
              "endmodule\n"));
}

TEST(ConstraintDeclParsing, LetPortItem_RegType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(reg [3:0] r) = r;\n"
              "endmodule\n"));
}

TEST(ConstraintDeclParsing, LetPortItem_AttributeInstance) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f((* my_attr *) logic x) = x;\n"
              "endmodule\n"));
}

TEST(ConstraintDeclParsing, LetPortItem_AttributeInstanceMultiple) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f((* a = 1 *) x, (* b *) y) = x + y;\n"
              "endmodule\n"));
}

TEST(ConstraintDeclParsing, LetFormalType_Implicit) {
  auto r = Parse(
      "module m;\n"
      "  let f(x) = x;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->func_args[0].name, "x");
}

TEST(ConstraintDeclParsing, LetFormalType_Logic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(logic x) = x;\n"
              "endmodule\n"));
}

TEST(ConstraintDeclParsing, LetFormalType_LogicPacked) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(logic [31:0] x) = x;\n"
              "endmodule\n"));
}

TEST(ConstraintDeclParsing, LetFormalType_Integer) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(integer x) = x;\n"
              "endmodule\n"));
}

TEST(ConstraintDeclParsing, LetFormalType_Real) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(real x) = x;\n"
              "endmodule\n"));
}

TEST(ConstraintDeclParsing, LetFormalType_SignedImplicit) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(signed [7:0] x) = x;\n"
              "endmodule\n"));
}

TEST(ConstraintDeclParsing, LetFormalType_UnsignedImplicit) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(unsigned [7:0] x) = x;\n"
              "endmodule\n"));
}

TEST(ConstraintDeclParsing, LetFormalType_MixedUntypedAndTyped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(untyped a, logic [7:0] b) = b;\n"
              "endmodule\n"));
}

}  // namespace
