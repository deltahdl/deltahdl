#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DeclarationAssignmentParsing, NetDeclAssignmentBasic) {
  auto r = Parse("module m; wire w; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "w");
  EXPECT_EQ(item->init_expr, nullptr);
}

TEST(DeclarationAssignmentParsing, NetDeclAssignmentWithUnpackedDims) {
  auto r = Parse("module m; wire w [3:0][7:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "w");
  EXPECT_GE(item->unpacked_dims.size(), 1u);
}

TEST(DeclarationAssignmentParsing, ParamAssignmentBasic) {
  auto r = Parse("module m; parameter WIDTH = 8; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "WIDTH");
  EXPECT_NE(item->init_expr, nullptr);
}

// --- net_decl_assignment ---

TEST(DeclarationAssignmentParsing, NetDeclAssignmentWithInit) {
  auto r = Parse("module m; wire w = 1'b0; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "w");
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(DeclarationAssignmentParsing, NetDeclAssignmentWithDimsAndInit) {
  auto r = Parse("module m; wire [7:0] w [3:0] = '{default: 0}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "w");
  EXPECT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_NE(item->init_expr, nullptr);
}

// --- param_assignment ---

TEST(DeclarationAssignmentParsing, ParamAssignmentNoDefault) {
  auto r = Parse("module m #(parameter int P)(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "P");
}

TEST(DeclarationAssignmentParsing, ParamAssignmentWithUnpackedDims) {
  auto r = Parse(
      "module m;\n"
      "  parameter int P [0:3] = '{0, 1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "P");
  EXPECT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_NE(item->init_expr, nullptr);
}

// --- defparam_assignment ---

TEST(DeclarationAssignmentParsing, DefparamAssignmentBasic) {
  auto r = Parse(
      "module child; parameter P = 1; endmodule\n"
      "module m; child c(); defparam c.P = 5; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[1]->items) {
    if (item->kind == ModuleItemKind::kDefparam) {
      found = true;
      EXPECT_EQ(item->defparam_assigns.size(), 1u);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DeclarationAssignmentParsing, DefparamAssignmentMintypmax) {
  auto r = Parse(
      "module child; parameter P = 1; endmodule\n"
      "module m; child c(); defparam c.P = 1:2:3; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- pulse_control_specparam ---

TEST(DeclarationAssignmentParsing, PulseControlSpecparamRejectOnly) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$ = (2);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DeclarationAssignmentParsing, PulseControlSpecparamRejectAndError) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$ = (2, 5);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DeclarationAssignmentParsing, PulseControlSpecparamPathSpecific) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "    specparam PATHPULSE$a$b = (1, 2);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- type_assignment ---

TEST(DeclarationAssignmentParsing, TypeAssignmentWithDefault) {
  auto r = Parse("module m #(parameter type T = int)(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "T");
}

TEST(DeclarationAssignmentParsing, TypeAssignmentNoDefault) {
  auto r = Parse("module m #(parameter type T)(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "T");
}

TEST(DeclarationAssignmentParsing, TypeAssignmentComplexType) {
  auto r = Parse(
      "module m;\n"
      "  parameter type T = logic [7:0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
}

// --- variable_decl_assignment ---

TEST(DeclarationAssignmentParsing, VarDeclAssignmentBasic) {
  auto r = Parse("module m; int x = 5; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "x");
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(DeclarationAssignmentParsing, VarDeclAssignmentWithDims) {
  auto r = Parse("module m; int x [3:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "x");
  EXPECT_GE(item->unpacked_dims.size(), 1u);
}

TEST(DeclarationAssignmentParsing, VarDeclAssignmentDynamicArray) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  int d[];\n"
      "  initial d = new[10];\n"
      "endmodule\n"));
}

TEST(DeclarationAssignmentParsing, VarDeclAssignmentDynamicArrayWithInit) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  int src[], d[];\n"
      "  initial d = new[10](src);\n"
      "endmodule\n"));
}

TEST(DeclarationAssignmentParsing, VarDeclAssignmentClassNew) {
  EXPECT_TRUE(ParseOk(
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "  C c = new;\n"
      "endmodule\n"));
}

TEST(DeclarationAssignmentParsing, VarDeclAssignmentClassNewWithArgs) {
  EXPECT_TRUE(ParseOk(
      "class C;\n"
      "  function new(int a, int b); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c = new(1, 2);\n"
      "endmodule\n"));
}

// --- class_new ---

TEST(DeclarationAssignmentParsing, ClassNewNoArgs) {
  EXPECT_TRUE(ParseOk(
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "  C c = new;\n"
      "endmodule\n"));
}

TEST(DeclarationAssignmentParsing, ClassNewWithParenArgs) {
  EXPECT_TRUE(ParseOk(
      "class C;\n"
      "  function new(int x); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c = new(42);\n"
      "endmodule\n"));
}

// --- dynamic_array_new ---

TEST(DeclarationAssignmentParsing, DynamicArrayNewSizeOnly) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  int d[];\n"
      "  initial d = new[100];\n"
      "endmodule\n"));
}

TEST(DeclarationAssignmentParsing, DynamicArrayNewSizeAndSource) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  int src[], dst[];\n"
      "  initial dst = new[20](src);\n"
      "endmodule\n"));
}

}  // namespace
