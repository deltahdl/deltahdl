#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA213, DataDeclBasicVar) {
  auto r = Parse("module m; logic [7:0] data; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "data");
}

TEST(ParserA213, DataDeclVarPrefix) {
  auto r = Parse("module m; var logic x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
}

TEST(ParserA213, DataDeclLifetimeAutomatic) {
  auto r = Parse("module m; automatic int counter; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_TRUE(item->is_automatic);
}

TEST(ParserA213, DataDeclLifetimeStatic) {
  auto r = Parse("module m; static int counter; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_TRUE(item->is_static);
}

TEST(ParserA23, ListOfVariableDeclAssignmentsSingle) {
  auto r = Parse("module m; int x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kVarDecl);
}

TEST(ParserA23, ListOfVariableDeclAssignmentsMultiple) {
  auto r = Parse("module m; int a = 1, b = 2, c = 3; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kVarDecl) count++;
  }
  EXPECT_GE(count, 3);
}

TEST(ParserA24, VarDeclAssignmentBasic) {
  auto r = Parse("module m; int x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "x");
  EXPECT_EQ(item->init_expr, nullptr);
}

TEST(ParserA28, DataDeclMultiVarsInBlock) {
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

TEST(ParserAnnexA, A2VarDeclWithInit) {
  auto r = Parse("module m; logic [7:0] data = 8'hFF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_NE(r.cu->modules[0]->items[0]->init_expr, nullptr);
}

TEST(ParserA213, DataDeclMultipleAssign) {
  auto r = Parse("module m; int a = 1, b = 2; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kVarDecl) count++;
  }
  EXPECT_GE(count, 2);
}

TEST(ParserA221, DataTypeScopedType) {
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

TEST(ParserA23, ListOfVariableDeclAssignmentsWithDims) {
  auto r = Parse("module m; logic [7:0] mem [256], cache [64]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kVarDecl) count++;
  }
  EXPECT_GE(count, 2);
}

TEST(ParserSection6, Sec6_5_IntVarDeclKind) {
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

TEST(ParserSection6, Sec6_5_LogicVarInit) {
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

TEST(ParserSection6, Sec6_11_MultipleVarsWithPackedDims) {
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

TEST(ParserSection6, Sec6_5_MultipleLogicDecls) {
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

TEST(ParserSection6, Sec6_11_ByteWithInitializer) {
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

TEST(ParserSection6, VarKeywordLogicDecl) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  var logic [7:0] data;\n"
              "endmodule\n"));
}

TEST(ParserSection6, MultipleIntDeclsCommaSeparated) {
  auto r = Parse(
      "module m;\n"
      "  int a, b, c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
}

TEST(ParserSection6, VarKeywordImplicitType) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  var [3:0] nibble;\n"
              "endmodule\n"));
}
TEST(ParserSection6, IntWithInitializer) {
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

TEST(ParserSection6, VarWithEnumType) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  var enum bit { clear, error } status;\n"
              "endmodule\n"));
}

TEST(ParserSection6, Sec6_11_IntWithComplexInit) {
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

TEST(ParserSection6, Sec6_11_IntegerAndRealCoexist) {
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

TEST(ParserSection6, VarRegDecl) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  var reg r;\n"
              "endmodule\n"));
}

TEST(ParserSection6, VarImplicitInProcedural) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    var [3:0] x;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection6, MixedIntegerRealStringTypes) {
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

TEST(ParserSection6, IntegerTypesInProcedural) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    byte b;\n"
              "    shortint si;\n"
              "    int i;\n"
              "    longint li;\n"
              "    integer ig;\n"
              "    bit bv;\n"
              "    logic l;\n"
              "    reg r;\n"
              "    time t;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection6, RealWithInitializer) {
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

TEST(ParserSection6, ShortrealWithInitializer) {
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

// §6.8: var byte my_byte — equivalent to "byte my_byte".
TEST(ParserSection6, Sec6_8_VarByteDecl) {
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

// §6.8: var [15:0] vw — equivalent to "var logic [15:0] vw".
TEST(ParserSection6, Sec6_8_VarImplicitLogicWithRange) {
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

// §6.8: shortint s1, s2[0:9] — mixed scalar and array.
TEST(ParserSection6, Sec6_8_MixedScalarAndArrayDecl) {
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

// §6.8: const variable declaration.
TEST(ParserSection6, Sec6_8_ConstVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  const int MAX = 100;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_TRUE(item->data_type.is_const);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->name, "MAX");
  EXPECT_NE(item->init_expr, nullptr);
}

// §6.8: Variable with initializer — int i = 0.
TEST(ParserSection6, Sec6_8_IntInitZero) {
  auto r = Parse(
      "module t;\n"
      "  int i = 0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->name, "i");
  ASSERT_NE(item->init_expr, nullptr);
  EXPECT_EQ(item->init_expr->int_val, 0u);
}

// §6.8: input var logic port declaration.
TEST(ParserSection6, Sec6_8_InputVarLogicPort) {
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

}  // namespace
