#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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

TEST(TypeParameterParsing, TypeParamDefaultLogicVector) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter type DATA_T = logic [15:0])\n"
              "  ();\n"
              "  DATA_T data;\n"
              "endmodule\n"));
}

TEST(TypeParameterParsing, TypeParamPort) {
  EXPECT_TRUE(ParseOk6("module top #(type T = real); endmodule\n"));
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

}  // namespace
