#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {}

TEST(ParameterDeclParsing, LocalparamExplicitType) {
  auto r = Parse("module m; localparam int X = 5; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_TRUE(item->is_localparam);
  EXPECT_EQ(item->name, "X");
}

TEST(ParameterDeclParsing, LocalparamImplicitType) {
  auto r = Parse("module m; localparam X = 42; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "X");
}

TEST(ParameterDeclParsing, LocalparamPackedDimImplicit) {
  auto r = Parse("module m; localparam [7:0] MASK = 8'hFF; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
}

TEST(ParameterDeclParsing, LocalparamTypeParam) {
  auto r = Parse("module m; localparam type T = int; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kVoid);
}

TEST(ParameterDeclParsing, ParameterExplicitType) {
  auto r = Parse("module m; parameter int WIDTH = 8; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_FALSE(item->is_localparam);
  EXPECT_EQ(item->name, "WIDTH");
}

TEST(ParameterDeclParsing, ParameterImplicitType) {
  auto r = Parse("module m; parameter SIZE = 16; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
}

TEST(ParameterDeclParsing, ParameterPackedDim) {
  auto r = Parse("module m; parameter [31:0] ADDR = 0; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
}

TEST(ParameterDeclParsing, ParameterTypeParam) {
  auto r = Parse("module m; parameter type BusType = logic [7:0]; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kVoid);
}

TEST(ParameterDeclParsing, ParameterStringType) {
  auto r = Parse("module m; parameter string NAME = \"hello\"; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParameterDeclParsing, ParameterRealType) {
  auto r = Parse("module m; parameter real PI = 3.14; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParameterDeclParsing, TypeParamForwardEnum) {
  auto r = Parse("module m; parameter type enum E = my_enum_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "E");
}

TEST(ParameterDeclParsing, TypeParamForwardStruct) {
  auto r = Parse("module m; parameter type struct S = my_struct_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "S");
}

TEST(ParameterDeclParsing, TypeParamForwardUnion) {
  auto r = Parse("module m; parameter type union U = my_union_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "U");
}

TEST(ParameterDeclParsing, TypeParamForwardClass) {
  auto r = Parse("module m; parameter type class C = my_class_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "C");
}

TEST(ParameterDeclParsing, TypeParamForwardInterfaceClass) {
  auto r = Parse(
      "module m;\n"
      "  parameter type interface class IC = my_ifc_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "IC");
}

TEST(ParameterDeclParsing, ListOfParamAssignments) {
  auto r = Parse("module m; parameter int A = 1, B = 2, C = 3; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int param_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) param_count++;
  }
  EXPECT_GE(param_count, 3);
}

TEST(ParameterDeclParsing, ListOfLocalparamAssignments) {
  auto r = Parse("module m; localparam int X = 10, Y = 20; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int param_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) param_count++;
  }
  EXPECT_GE(param_count, 2);
}

TEST(ParameterDeclParsing, ListOfTypeAssignments) {
  auto r = Parse("module m; parameter type T1 = int, T2 = real; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int param_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) param_count++;
  }
  EXPECT_GE(param_count, 2);
}

TEST(ParameterDeclParsing, SpecparamBasic) {
  auto r = Parse(
      "module m;\n"
      "  specify specparam tRISE = 100; endspecify\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParameterDeclParsing, SpecparamPackedDim) {
  auto r = Parse(
      "module m;\n"
      "  specify specparam [31:0] tDELAY = 50; endspecify\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParameterDeclParsing, SpecparamMultipleAssignments) {
  auto r = Parse(
      "module m;\n"
      "  specify specparam tRISE = 100, tFALL = 50; endspecify\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParameterDeclParsing, SpecparamOutsideSpecify) {
  auto r = Parse("module m; specparam tPD = 10; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kSpecparam);
}

TEST(ParameterDeclParsing, ParamAssignmentNoDefault) {
  auto r = Parse("module m #(parameter int P)(); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
// Edge cases

TEST(ParameterDeclParsing, ParameterSignedType) {
  auto r = Parse("module m; parameter signed [7:0] S = -1; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "S");
}

TEST(ParameterDeclParsing, LocalparamSignedType) {
  auto r = Parse("module m; localparam signed [3:0] N = 4'sb1111; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
}

TEST(ParameterDeclParsing, ParameterLogicVectorType) {
  auto r = Parse("module m; parameter logic [15:0] ADDR = 16'hBEEF; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "ADDR");
}

TEST(ParameterDeclParsing, ParameterIntegerType) {
  auto r = Parse("module m; parameter integer COUNT = 100; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
}

TEST(ParameterDeclParsing, SpecparamMintypmax) {
  auto r = Parse(
      "module m;\n"
      "  specify specparam tRISE = 1:2:3; endspecify\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParameterDeclParsing, SpecparamPathpulse) {
  auto r = Parse(
      "module m;\n"
      "  specify specparam PATHPULSE$ = (1, 2); endspecify\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParameterDeclParsing, ParameterExpressionDefault) {
  auto r = Parse("module m; parameter int HALF = 16 / 2; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "HALF");
}

TEST(ParameterDeclParsing, LocalparamExpressionReferenceOther) {
  auto r = Parse(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "  localparam int DEPTH = 2 ** WIDTH;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int param_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) param_count++;
  }
  EXPECT_EQ(param_count, 2);
}

TEST(ParameterDeclParsing, TypeParamNoDefault) {
  auto r = Parse("module m #(parameter type T)(); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Error conditions

TEST(ParameterDeclParsing, ErrorParameterMissingSemicolon) {
  auto r = Parse("module m; parameter int X = 5 endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParameterDeclParsing, ErrorLocalparamMissingSemicolon) {
  auto r = Parse("module m; localparam int Y = 10 endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParameterDeclParsing, ErrorSpecparamMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  specify specparam tRISE = 100 endspecify\n"
      "endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParameterDeclParsing, ErrorParameterMissingEquals) {
  auto r = Parse("module m; parameter int X; endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParameterDeclParsing, ErrorLocalparamMissingEquals) {
  auto r = Parse("module m; localparam int Y; endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(FormalSyntaxParsing, ParamDecl) {
  auto r = Parse(
      "module m;\n"
      "  parameter int WIDTH = 16;\n"
      "  localparam int DEPTH = 32;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(r.cu->modules[0]->items[1]->kind, ModuleItemKind::kParamDecl);
}
