#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(VariableDeclaration, DataDeclBasicVar) {
  auto r = Parse("module m; logic [7:0] data; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "data");
}

TEST(VariableDeclaration, DataDeclVarPrefix) {
  auto r = Parse("module m; var logic x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
}

TEST(DeclarationListParsing, ListOfVariableDeclAssignmentsOneDeclPerElement) {
  auto r = Parse("module m; int a = 1, b = 2, c = 3; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kVarDecl) count++;
  }
  EXPECT_GE(count, 3);
}

TEST(BlockItemDeclParsing, DataDeclMultiVarsInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int a = 1, b = 2, c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->var_name, "a");
  EXPECT_EQ(body->stmts[1]->var_name, "b");
  EXPECT_EQ(body->stmts[2]->var_name, "c");
}

TEST(VariableDeclaration, DataTypeScopedType) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef int my_int_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "  pkg::my_int_t x;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DeclarationListParsing, ListOfVariableDeclAssignmentsWithDims) {
  auto r = Parse("module m; logic [7:0] mem [256], cache [64]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kVarDecl) count++;
  }
  EXPECT_GE(count, 2);
}

TEST(DataTypeParsing, IntVarDeclKind) {
  auto r = Parse(
      "module t;\n"
      "  int count;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_FALSE(item->data_type.is_net);
  EXPECT_EQ(item->name, "count");
}

TEST(DataTypeParsing, LogicVarInit) {
  auto r = Parse(
      "module t;\n"
      "  logic v = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(item->data_type.is_net);
  ASSERT_NE(item->init_expr, nullptr);
}

TEST(DataTypeParsing, MultipleVarsWithPackedDims) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->name, "a");
  EXPECT_EQ(items[1]->name, "b");
  EXPECT_EQ(items[2]->name, "c");
  for (auto* item : items) {
    EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
    ASSERT_NE(item->data_type.packed_dim_left, nullptr);
    EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
  }
}

TEST(DataTypeParsing, MultipleLogicDecls) {
  auto r = Parse(
      "module t;\n"
      "  logic x, y, z;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  for (auto* item : items) {
    EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
    EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
    EXPECT_FALSE(item->data_type.is_net);
  }
  EXPECT_EQ(items[0]->name, "x");
  EXPECT_EQ(items[1]->name, "y");
  EXPECT_EQ(items[2]->name, "z");
}

TEST(DataTypeParsing, ByteWithInitializer) {
  auto r = Parse(
      "module t;\n"
      "  byte b = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(item->name, "b");
  ASSERT_NE(item->init_expr, nullptr);
}

TEST(DataTypeParsing, IntWithInitializer) {
  auto r = Parse(
      "module m;\n"
      "  int x = 42;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(DataTypeParsing, VarWithEnumType) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  var enum bit { clear, error } status;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, IntWithComplexInit) {
  auto r = Parse(
      "module t;\n"
      "  int x = 1 + 2 * 3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->name, "x");
  ASSERT_NE(item->init_expr, nullptr);
  EXPECT_EQ(item->init_expr->kind, ExprKind::kBinary);
}

TEST(DataTypeParsing, IntegerAndRealCoexist) {
  auto r = Parse(
      "module t;\n"
      "  int count;\n"
      "  real voltage;\n"
      "  byte flags;\n"
      "  shortreal gain;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 4u);
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(items[1]->data_type.kind, DataTypeKind::kReal);
  EXPECT_EQ(items[2]->data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(items[3]->data_type.kind, DataTypeKind::kShortreal);
}

TEST(DataTypeParsing, VarRegDecl) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  var reg r;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, MixedIntegerRealStringTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int i;\n"
              "  real r;\n"
              "  shortreal sr;\n"
              "  string s;\n"
              "  byte b;\n"
              "  logic [7:0] l;\n"
              "  integer ig;\n"
              "  realtime rt;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, RealWithInitializer) {
  auto r = Parse(
      "module m;\n"
      "  real pi = 3.14159;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReal);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(DataTypeParsing, ShortrealWithInitializer) {
  auto r = Parse(
      "module m;\n"
      "  shortreal f = 1.5;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortreal);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(DataTypeParsing, VarByteDecl) {
  auto r = Parse(
      "module t;\n"
      "  var byte my_byte;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(item->name, "my_byte");
}

TEST(DataTypeParsing, VarImplicitLogicWithRange) {
  auto r = Parse(
      "module t;\n"
      "  var [15:0] vw;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "vw");
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 15u);
}

TEST(DataTypeParsing, VarSignedRangeImplicitType) {
  auto r = Parse(
      "module t;\n"
      "  var signed [7:0] v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kImplicit);
  EXPECT_TRUE(item->data_type.is_signed);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->name, "v");
}

TEST(DataTypeParsing, MixedScalarAndArrayDecl) {
  auto r = Parse(
      "module t;\n"
      "  shortint s1, s2 [0:9];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[0]->name, "s1");
  EXPECT_TRUE(items[0]->unpacked_dims.empty());
  EXPECT_EQ(items[1]->name, "s2");
  EXPECT_FALSE(items[1]->unpacked_dims.empty());
}

TEST(DataTypeParsing, InputVarLogicPort) {
  auto r = Parse(
      "module t(input var logic data_in);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_GE(ports.size(), 1u);
  EXPECT_EQ(ports[0].name, "data_in");
  EXPECT_EQ(ports[0].direction, Direction::kInput);
}

TEST(ImplicitDataType, ImplicitDataType) {
  auto r = Parse("module m(input [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_NE(port.data_type.packed_dim_left, nullptr);
}

TEST(ImplicitDataType, ImplicitDataTypeSigned) {
  auto r = Parse("module m(input signed [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_TRUE(port.data_type.is_signed);
}

TEST(VariableDeclarations, VarBareNoTypeIsValid) {
  auto r = Parse(
      "module m;\n"
      "  var v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "v");
}

TEST(VariableDeclarations, AutomaticWithoutDataTypeOrVarIsError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic x = 0;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "data_declaration without an explicit data type "
                            "requires the 'var' keyword",
                            3, "6.8"));
}

TEST(VariableDeclarations, StaticWithoutDataTypeOrVarIsError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    static y = 0;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "data_declaration without an explicit data type "
                            "requires the 'var' keyword",
                            3, "6.8"));
}

TEST(VariableDeclarations, StaticAtModuleScopeWithoutDataTypeOrVarIsError) {
  auto r = Parse(
      "module m;\n"
      "  static x = 0;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "data_declaration without an explicit data type "
                            "requires the 'var' keyword",
                            2, "6.8"));
}

TEST(VariableDeclarations, AutomaticAtModuleScopeWithoutDataTypeOrVarIsError) {
  auto r = Parse(
      "module m;\n"
      "  automatic x = 0;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "data_declaration without an explicit data type "
                            "requires the 'var' keyword",
                            2, "6.8"));
}

TEST(VariableDeclarations, ImplicitTypeAtModuleScopeWithoutVarIsError) {
  auto r = Parse(
      "module m;\n"
      "  signed [3:0] x;\n"
      "  unsigned u;\n"
      "  const c = 1;\n"
      "  const signed [3:0] k = 2;\n"
      "  automatic signed [3:0] a;\n"
      "  var signed [3:0] vx;\n"
      "  const var cv = 1;\n"
      "  int i;\n"
      "endmodule\n");
  for (uint32_t line : {2U, 3U, 4U, 5U, 6U}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "data_declaration without an explicit data type "
                              "requires the 'var' keyword",
                              line, "6.8"));
  }
  for (uint32_t line : {7U, 8U, 9U}) {
    EXPECT_FALSE(
        ReportedError(r.diags, "requires the 'var' keyword", line, "6.8"));
  }
}

TEST(VariableDeclarations, AutomaticVarWithoutDataTypeOk) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    var automatic x = 1'b0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(VariableDeclarations, VarWithUnpackedArrayDim) {
  auto r = Parse(
      "module m;\n"
      "  int mem [256];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "mem");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

TEST(VariableDeclarations, TypeRefInVarDeclWithoutVarIsError) {
  auto r = Parse(
      "module m;\n"
      "  int a;\n"
      "  type(a) b;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "type_reference in a variable declaration must be "
                            "preceded by the 'var' keyword",
                            3, "6.8"));
}

TEST(VariableDeclarations, TypeRefInVarDeclWithVarOk) {
  auto r = Parse(
      "module m;\n"
      "  int a;\n"
      "  var type(a) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_NE(item->data_type.type_ref_expr, nullptr);
  EXPECT_EQ(item->name, "b");
}

TEST(VariableDeclarations, TypeRefInNetDeclWithWireOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire x;\n"
              "  wire type(x) y;\n"
              "endmodule\n"));
}

TEST(ImplicitDataType, ImplicitDataTypeUnsigned) {
  auto r = Parse("module m(input unsigned [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_FALSE(port.data_type.is_signed);
}

TEST(DataTypeParsing, UnsignedOnLogicVectorOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic unsigned [7:0] data;\n"
              "endmodule\n"));
}

TEST(VariableDeclaration, DynamicArrayVarDeclNew) {
  auto r = Parse(
      "module m;\n"
      "  int da [] = new[4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(VariableDeclarations, TypeRefBareWithoutNetTypeOrVarIsError) {
  auto r = Parse(
      "module m;\n"
      "  wire x;\n"
      "  type(x) y;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "type_reference in a variable declaration must be "
                            "preceded by the 'var' keyword",
                            3, "6.8"));
}

TEST(DataTypeParsing, ClassTypeVarDecl) {
  auto r = Parse(
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "  C handle;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "handle");
}

TEST(DataTypeParsing, VirtualInterfaceVarDecl) {
  auto r = Parse(
      "interface bus_if;\n"
      "endinterface\n"
      "module m;\n"
      "  virtual bus_if vi;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "vi");
}

TEST(DataTypeParsing, VirtualInterfaceWithKeywordVarDecl) {
  auto r = Parse(
      "interface bus_if;\n"
      "endinterface\n"
      "module m;\n"
      "  virtual interface bus_if vi;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(VariableDeclaration, ClassHandleVarDeclWithNew) {
  auto r = Parse(
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "  C handle = new();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "handle");
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(VariableDeclaration, PackageScopedTypedefWithPackedDimension) {
  auto r = Parse(
      "package pk;\n"
      "  typedef struct packed { logic a; logic [1:0] b; } ps_t;\n"
      "endpackage\n"
      "module m; pk::ps_t [1:0] pv; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[0]->name, "pv");
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(items[0]->data_type.scope_name, "pk");
  EXPECT_EQ(items[0]->data_type.type_name, "ps_t");
  ASSERT_NE(items[0]->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(items[0]->data_type.packed_dim_left->int_val, 1u);
}

constexpr std::string_view kVarRequired =
    "data_declaration without an explicit data type requires the 'var' "
    "keyword";

TEST(VariableDeclarations, DISABLED_BareNameDeclarationIsErrorInEveryPlace) {
  auto r = Parse(
      "module m;\n"
      "  x;\n"
      "  y = 1;\n"
      "  int w;\n"
      "  w = 1;\n"
      "endmodule\n"
      "interface i;\n"
      "  x;\n"
      "  y = 1;\n"
      "  int w;\n"
      "  w = 1;\n"
      "endinterface\n"
      "program p;\n"
      "  x;\n"
      "  y = 1;\n"
      "endprogram\n"
      "checker c;\n"
      "  x;\n"
      "  y = 1;\n"
      "  int w;\n"
      "  w = 1;\n"
      "endchecker\n"
      "package k;\n"
      "  x;\n"
      "  y = 1;\n"
      "endpackage\n"
      "module g;\n"
      "  if (1) begin : b\n"
      "    x;\n"
      "    y = 1;\n"
      "  end\n"
      "endmodule\n");
  for (uint32_t line :
       {2U, 3U, 5U, 8U, 9U, 11U, 14U, 15U, 18U, 19U, 21U, 24U, 25U, 29U, 30U}) {
    EXPECT_TRUE(ReportedError(r.diags, kVarRequired, line, "6.8"));
  }
}

TEST(VariableDeclarations, DISABLED_BareNameAtCompilationUnitIsReportedAsSuch) {
  auto r = Parse(
      "x;\n"
      "y = 1;\n");
  EXPECT_TRUE(ReportedError(r.diags, kVarRequired, 1, "6.8"));
  EXPECT_TRUE(ReportedError(r.diags, kVarRequired, 2, "6.8"));
}

TEST(VariableDeclarations, BareNameWithVarOrADataTypeIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  var x = 1;\n"
      "  logic y = 1;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(VariableDeclarations, DISABLED_PackedDimensionsAloneIsErrorInEveryPlace) {
  auto r = Parse(
      "[3:0] cu;\n"
      "module m;\n"
      "  [3:0] x;\n"
      "  if (1) begin : b\n"
      "    [3:0] y;\n"
      "  end\n"
      "  initial begin\n"
      "    [3:0] z;\n"
      "  end\n"
      "endmodule\n"
      "interface i;\n"
      "  [7:0] x;\n"
      "endinterface\n"
      "program p;\n"
      "  [3:0] x;\n"
      "endprogram\n"
      "checker c;\n"
      "  [3:0] x;\n"
      "endchecker\n"
      "package k;\n"
      "  [3:0] x;\n"
      "endpackage\n");
  for (uint32_t line : {1U, 3U, 5U, 8U, 12U, 15U, 18U, 21U}) {
    EXPECT_TRUE(ReportedError(r.diags, kVarRequired, line, "6.8"));
  }
}

TEST(VariableDeclarations, SigningAloneIsErrorInADesignElementOrPackage) {
  auto r = Parse(
      "interface i;\n"
      "  signed x;\n"
      "endinterface\n"
      "program p;\n"
      "  signed x;\n"
      "endprogram\n"
      "checker c;\n"
      "  signed x;\n"
      "endchecker\n"
      "package k;\n"
      "  signed x;\n"
      "endpackage\n"
      "module m;\n"
      "  if (1) begin : b\n"
      "    signed y;\n"
      "  end\n"
      "endmodule\n");
  for (uint32_t line : {2U, 5U, 8U, 11U, 15U}) {
    EXPECT_TRUE(ReportedError(r.diags, kVarRequired, line, "6.8"));
  }
}

TEST(VariableDeclarations,
     DISABLED_SigningAloneIsErrorInCompilationUnitAndProcedure) {
  auto r = Parse(
      "signed cu;\n"
      "module m;\n"
      "  initial begin\n"
      "    signed z;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, kVarRequired, 1, "6.8"));
  EXPECT_TRUE(ReportedError(r.diags, kVarRequired, 4, "6.8"));
}

TEST(VariableDeclarations, VarWithImplicitTypeIsAcceptedInEveryPlace) {
  auto r = Parse(
      "var [3:0] cu;\n"
      "interface i;\n"
      "  var [7:0] x;\n"
      "endinterface\n"
      "program p;\n"
      "  var signed x;\n"
      "endprogram\n"
      "checker c;\n"
      "  var [7:0] x;\n"
      "endchecker\n"
      "package k;\n"
      "  var signed y;\n"
      "endpackage\n"
      "module m;\n"
      "  if (1) begin : b\n"
      "    var [7:0] x;\n"
      "  end\n"
      "  initial begin\n"
      "    var signed [7:0] y;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(VariableDeclarations, TypeRefWithoutVarIsErrorInEveryPlace) {
  auto r = Parse(
      "package p;\n"
      "  int a;\n"
      "  type(a) b;\n"
      "endpackage\n"
      "class C;\n"
      "  int a;\n"
      "  type(a) b;\n"
      "endclass\n"
      "interface i;\n"
      "  logic a;\n"
      "  type(a) b;\n"
      "endinterface\n"
      "module t;\n"
      "  int a;\n"
      "  initial begin\n"
      "    type(a) b;\n"
      "  end\n"
      "endmodule\n");
  for (uint32_t line : {3U, 7U, 11U, 16U}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "type_reference in a variable declaration must "
                              "be preceded by the 'var' keyword",
                              line, "6.8"));
  }
}

TEST(VariableDeclarations, TypeRefAfterVarOrANetTypeIsAcceptedInEveryPlace) {
  auto r = Parse(
      "package p;\n"
      "  int a;\n"
      "  var type(a) b;\n"
      "endpackage\n"
      "class C;\n"
      "  int a;\n"
      "  var type(a) b;\n"
      "endclass\n"
      "interface i;\n"
      "  logic a;\n"
      "  var type(a) b;\n"
      "  wire type(a) w;\n"
      "endinterface\n"
      "module t;\n"
      "  logic a;\n"
      "  wire type(a) w;\n"
      "  initial begin\n"
      "    var type(a) v;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
