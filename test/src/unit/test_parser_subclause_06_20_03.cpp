#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;
namespace {

TEST(TypeParameterParsing, PortListTypeParamParses) {
  auto r = Parse("module m #(type T = int); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "T");
}

TEST(TypeParameterParsing, TypeParamWithoutDefaultParses) {
  auto r = Parse("module m #(parameter type T); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TypeParameterParsing, BodyTypeParamWithLogicVectorParses) {
  auto r = Parse("module m; parameter type T = logic [7:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TypeParameterParsing, TypeParamWithIntDefaultAndUsageParses) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter type T = int);\n"
              "  T data;\n"
              "endmodule\n"));
}

TEST(TypeParameterParsing, TypeParameterLogicVector) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter type T = logic [7:0]);\n"
              "  T bus;\n"
              "endmodule\n"));
}

TEST(TypeParameterParsing, LocalparamTypeDecl) {
  EXPECT_TRUE(
      ParseOk6("module t;\n"
               "  localparam type testtype = logic;\n"
               "  testtype x;\n"
               "endmodule\n"));
}

TEST(TypeParameterParsing, TypeParameterWithMultipleParams) {
  EXPECT_TRUE(
      ParseOk6("module m #(parameter type T = int, parameter type U = real)\n"
               "  ();\n"
               "  T x;\n"
               "  U y;\n"
               "endmodule\n"));
}

TEST(TypeParameterParsing, MixedValueAndTypeParamsParses) {
  EXPECT_TRUE(
      ParseOk6("module ma #(parameter p1 = 1, parameter type p2 = shortint)\n"
               "  (input logic [p1:0] i, output logic [p1:0] o);\n"
               "  p2 j = 0;\n"
               "endmodule\n"));
}

TEST(TypeParameterParsing, PortListForwardEnumParses) {
  EXPECT_TRUE(
      ParseOk6("module m #(type enum T = logic);\n"
               "endmodule\n"));
}

TEST(TypeParameterParsing, TypeParamWithStructRestriction) {
  EXPECT_TRUE(
      ParseOk6("module m #(type struct T);\n"
               "endmodule\n"));
}

TEST(TypeParameterParsing, TypeParamForwardEnum) {
  auto r = Parse("module m; parameter type enum E = my_enum_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "E");
}

TEST(TypeParameterParsing, TypeParamForwardUnion) {
  auto r = Parse("module m; parameter type union U = my_union_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "U");
}

TEST(TypeParameterParsing, TypeParamForwardClass) {
  auto r = Parse("module m; parameter type class C = my_class_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "C");
}

TEST(TypeParameterParsing, TypeParamForwardInterfaceClass) {
  auto r = Parse(
      "module m;\n"
      "  parameter type interface class IC = my_ifc_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "IC");
}

TEST(TypeParameterParsing, CommaSeparatedTypeParamsParses) {
  auto r = Parse("module m; parameter type T1 = int, T2 = real; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int param_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) param_count++;
  }
  EXPECT_GE(param_count, 2);
}

TEST(TypeParameterParsing, TypeParamForwardStructBody) {
  auto r = Parse("module m; parameter type struct S = my_struct_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "S");
}

// A.1.3's parameter_port_declaration opens with `parameter`, `localparam`,
// `type` or a data type (printed page 1174 of ~/IEEE 1800-2023.pdf), so `B =
// logic` after the comma continues A.2.1.1's `type list_of_type_assignments`
// (printed pages 1181 and 1184) rather than opening a value parameter: B is a
// type parameter, and `B x;` in the body declares x. The same holds under the
// `parameter` keyword.
TEST(TypeParameterParsing, PortListTypeGroupContinuesPastTheComma) {
  auto r = Parse(
      "module m #(type A = int, B = logic);\n"
      "  B x;\n"
      "endmodule\n"
      "module n #(parameter type P = int, Q = real);\n"
      "  Q y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  auto* m = r.cu->modules[0];
  EXPECT_TRUE(m->type_param_names.count("A"));
  EXPECT_TRUE(m->type_param_names.count("B"));
  auto* x = FindItemByName(m->items, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(x->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(x->data_type.type_name, "B");
  auto* n = r.cu->modules[1];
  EXPECT_TRUE(n->type_param_names.count("Q"));
  auto* y = FindItemByName(n->items, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(y->data_type.type_name, "Q");
}

// A value group is still continued the same way: `B = 2` after
// `parameter int A = 1` is the second param_assignment of that declaration,
// and `C = 3` after `localparam type L = int` is a localparam type.
TEST(TypeParameterParsing, ValueGroupAfterATypeGroupContinuesAsValues) {
  auto r = Parse(
      "module m #(type T = int, parameter int A = 1, B = 2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* m = r.cu->modules[0];
  ASSERT_EQ(m->params.size(), 3u);
  EXPECT_EQ(m->params[2].first, "B");
  EXPECT_TRUE(m->type_param_names.count("T"));
  EXPECT_FALSE(m->type_param_names.count("A"));
  EXPECT_FALSE(m->type_param_names.count("B"));
}

}  // namespace
