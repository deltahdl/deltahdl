#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(LetDeclParsing, LetDecl_NoPorts) {
  auto r = Parse(
      "module m;\n"
      "  let answer = 42;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kLetDecl);
  EXPECT_EQ(item->name, "answer");
  ASSERT_NE(item->init_expr, nullptr);
  EXPECT_TRUE(item->func_args.empty());
}

TEST(LetDeclParsing, LetDecl_EmptyPortList) {
  auto r = Parse(
      "module m;\n"
      "  let zero() = 1'b0;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "zero");
  EXPECT_TRUE(item->func_args.empty());
}

TEST(LetDeclParsing, LetPortItem_TypedFormal) {
  auto r = Parse(
      "module m;\n"
      "  let half(int x) = x / 2;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "x");
}

TEST(LetDeclParsing, LetFormalType_UntypedAlternative) {
  auto r = Parse(
      "module m;\n"
      "  let same(untyped a) = a;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "a");
}

TEST(LetDeclParsing, LetFormalType_Implicit) {
  auto r = Parse(
      "module m;\n"
      "  let inc(a) = a + 1;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "a");
}

TEST(LetDeclParsing, LetFormalType_PackageScoped) {
  auto r = Parse(
      "package pc;\n"
      "  class P; endclass\n"
      "endpackage\n"
      "module m;\n"
      "  let same(pc::P x) = x;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "x");
  EXPECT_EQ(item->func_args[0].data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(item->func_args[0].data_type.scope_name, "pc");
  EXPECT_EQ(item->func_args[0].data_type.type_name, "P");
}

TEST(LetDeclParsing, LetPortList_RepeatedPortItems) {
  auto r = Parse(
      "module m;\n"
      "  let mux(sel, d0, d1) = sel ? d1 : d0;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 3u);
  EXPECT_EQ(item->func_args[0].name, "sel");
  EXPECT_EQ(item->func_args[1].name, "d0");
  EXPECT_EQ(item->func_args[2].name, "d1");
}

TEST(LetDeclParsing, LetPortItem_VariableDimension) {
  auto r = Parse(
      "module m;\n"
      "  let pick(int x [4]) = x[0];\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_FALSE(item->func_args[0].unpacked_dims.empty());
}

TEST(LetDeclParsing, LetPortItem_DefaultValue) {
  auto r = Parse(
      "module m;\n"
      "  let scaled(int x = 1) = x * 2;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_NE(item->func_args[0].default_value, nullptr);
}

TEST(LetDeclParsing, LetPortItem_WithAttribute) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f((* foo *) int x) = x;\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetExpression_PositionalArgs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let mux(sel, d0, d1) = sel ? d1 : d0;\n"
              "  wire w;\n"
              "  assign w = mux(s, a + 1, b);\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetExpression_NoArgs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let answer = 42;\n"
              "  wire [7:0] w;\n"
              "  assign w = answer;\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetListOfArguments_AllNamed) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let mux(sel, d0, d1) = sel ? d1 : d0;\n"
              "  wire w;\n"
              "  assign w = mux(.sel(s), .d0(a), .d1(b));\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetListOfArguments_PositionalThenNamed) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let mux(sel, d0, d1) = sel ? d1 : d0;\n"
              "  wire w;\n"
              "  assign w = mux(s, .d0(a), .d1(b));\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetListOfArguments_NamedEmptyArg) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let mux(sel, d0, d1) = sel ? d1 : d0;\n"
              "  wire w;\n"
              "  assign w = mux(.sel(s), .d0(), .d1(b));\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetExpression_PackageScope) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire w;\n"
              "  assign w = pkg::mux(s, a, b);\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetDecl_InProceduralBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    let twice(x) = x + x;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetPortItem_MultipleVariableDimensions) {
  auto r = Parse(
      "module m;\n"
      "  let first(int x [2][3]) = x[0][0];\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].unpacked_dims.size(), 2u);
}

TEST(LetDeclParsing, LetListOfArguments_PositionalEmptyArg) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let mux(sel, d0, d1) = sel ? d1 : d0;\n"
              "  wire w;\n"
              "  assign w = mux(, a, b);\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetExpression_PackageScopeNoArgs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire [7:0] w;\n"
              "  assign w = pkg::answer;\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, ErrorMissingAssignment) {
  auto r = Parse(
      "module m;\n"
      "  let bad(x);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected '=', got ';'", 2, "11.12"));
}

TEST(LetDeclParsing, ErrorMissingSemicolonNoPortList) {
  auto r = Parse(
      "module m;\n"
      "  let bad = 1\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 3, "11.12"));
}

TEST(LetDeclParsing, LetFormalOfATypeReference) {
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  let f(type(x) a) = a + 1;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_NE(item->func_args[0].data_type.type_ref_expr, nullptr);
}

TEST(LetDeclParsing, ALetFormalTakesNoConst) {
  auto r = Parse(
      "module m;\n"
      "  let f(const int x) = x + 1;\n"
      "  let g(int x) = x + 1;\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "a let formal takes no 'const'", 2, "A.2.12"));
  EXPECT_FALSE(
      ReportedError(r.diags, "a let formal takes no 'const'", 3, "A.2.12"));
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->func_args[0].name, "x");
}

TEST(LetDeclParsing, ALetFormalOfAnImplicitPackedType) {
  auto r = Parse(
      "module m;\n"
      "  let f([3:0] x) = x + 1;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  const DataType& type = item->func_args[0].data_type;
  EXPECT_EQ(type.kind, DataTypeKind::kImplicit);
  EXPECT_FALSE(type.signing_written);
  ASSERT_NE(type.packed_dim_left, nullptr);
  ASSERT_NE(type.packed_dim_right, nullptr);
  EXPECT_EQ(type.packed_dim_left->int_val, 3u);
  EXPECT_EQ(type.packed_dim_right->int_val, 0u);
  EXPECT_EQ(item->func_args[0].name, "x");
}

TEST(LetDeclParsing, ALetFormalOfAnInlineAggregateType) {
  auto r = Parse(
      "module m;\n"
      "  let f(struct packed { bit a; bit b; } s) = s.a;\n"
      "  let g(enum { A, B } e) = e == A;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  std::vector<const ModuleItem*> lets;
  for (const ModuleItem* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kLetDecl) lets.push_back(item);
  }
  ASSERT_EQ(lets.size(), 2u);
  ASSERT_EQ(lets[0]->func_args.size(), 1u);
  EXPECT_EQ(lets[0]->func_args[0].data_type.kind, DataTypeKind::kStruct);
  EXPECT_EQ(lets[0]->func_args[0].name, "s");
  ASSERT_EQ(lets[1]->func_args.size(), 1u);
  EXPECT_EQ(lets[1]->func_args[0].data_type.kind, DataTypeKind::kEnum);
  EXPECT_EQ(lets[1]->func_args[0].name, "e");
}

}  // namespace
