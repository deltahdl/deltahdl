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

TEST(DeclarationAssignmentParsing, NetDeclAssignmentWithInit) {
  auto r = Parse("module m; wire w = 1'b0; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "w");
  EXPECT_NE(item->init_expr, nullptr);
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

TEST(DeclarationAssignmentParsing, TypeAssignmentClassScopedType) {
  // type_assignment's right side admits
  // data_type_or_incomplete_class_scoped_type; exercise the class-scoped branch
  // (`C::inner_t`) rather than a plain data type.
  auto r = Parse(
      "class C;\n"
      "  typedef int inner_t;\n"
      "endclass\n"
      "module m;\n"
      "  parameter type T = C::inner_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "T");
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(item->typedef_type.scope_name, "C");
  EXPECT_EQ(item->typedef_type.type_name, "inner_t");
}

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
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int d[];\n"
              "  initial d = new[10];\n"
              "endmodule\n"));
}

TEST(DeclarationAssignmentParsing, VarDeclAssignmentDynamicArrayWithInit) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int src[], d[];\n"
              "  initial d = new[10](src);\n"
              "endmodule\n"));
}

TEST(DeclarationAssignmentParsing, VarDeclAssignmentClassNew) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "endclass\n"
              "module m;\n"
              "  C c = new;\n"
              "endmodule\n"));
}

TEST(DeclarationAssignmentParsing, VarDeclAssignmentClassNewWithArgs) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  function new(int a, int b); endfunction\n"
              "endclass\n"
              "module m;\n"
              "  C c = new(1, 2);\n"
              "endmodule\n"));
}

TEST(DeclarationAssignmentParsing, SpecparamAssignmentSimple) {
  auto r = Parse(
      "module m;\n"
      "  specparam delay = 5;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kSpecparam);
  EXPECT_EQ(item->name, "delay");
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(DeclarationAssignmentParsing, SpecparamAssignmentMintypmax) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  specparam delay = 1:2:3;\n"
              "endmodule\n"));
}

TEST(DeclarationAssignmentParsing, PulseControlSpecparamBareReject) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$ = (5);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->kind, ModuleItemKind::kSpecifyBlock);
  ASSERT_FALSE(item->specify_items.empty());
  auto* spi = item->specify_items[0];
  EXPECT_EQ(spi->kind, SpecifyItemKind::kSpecparam);
  EXPECT_TRUE(spi->is_pathpulse);
  EXPECT_TRUE(spi->pathpulse_input.empty());
  EXPECT_TRUE(spi->pathpulse_output.empty());
  EXPECT_NE(spi->pathpulse_reject, nullptr);
  EXPECT_EQ(spi->pathpulse_error, nullptr);
}

TEST(DeclarationAssignmentParsing, PulseControlSpecparamBareRejectAndError) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$ = (3, 7);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  auto* spi = item->specify_items[0];
  EXPECT_TRUE(spi->is_pathpulse);
  EXPECT_NE(spi->pathpulse_reject, nullptr);
  EXPECT_NE(spi->pathpulse_error, nullptr);
}

TEST(DeclarationAssignmentParsing, PulseControlSpecparamWithTerminals) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "    specparam PATHPULSE$a$b = (2, 4);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  auto* spi = item->specify_items[0];
  EXPECT_TRUE(spi->is_pathpulse);
  EXPECT_EQ(spi->pathpulse_input, "a");
  EXPECT_EQ(spi->pathpulse_output, "b");
  EXPECT_NE(spi->pathpulse_reject, nullptr);
  EXPECT_NE(spi->pathpulse_error, nullptr);
}

TEST(DeclarationAssignmentParsing, PulseControlSpecparamMintypmaxLimits) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  specify\n"
              "    specparam PATHPULSE$ = (1:2:3, 4:5:6);\n"
              "  endspecify\n"
              "endmodule\n"));
}

TEST(DeclarationAssignmentParsing, ClassNewCopyConstruct) {
  auto r = Parse(
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "  C a;\n"
      "  C b = new a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DeclarationAssignmentParsing, ClassNewScopedConstructor) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  function new(int x); endfunction\n"
              "endclass\n"
              "module m;\n"
              "  C c = C::new(7);\n"
              "endmodule\n"));
}

TEST(DeclarationAssignmentParsing, ClassNewEmptyParens) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  function new(); endfunction\n"
              "endclass\n"
              "module m;\n"
              "  C c = new();\n"
              "endmodule\n"));
}

TEST(DeclarationAssignmentParsing, SpecparamMissingEqualsIsError) {
  auto r = Parse(
      "module m;\n"
      "  specparam delay 5;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(DeclarationAssignmentParsing, DefparamMissingEqualsIsError) {
  auto r = Parse(
      "module child; parameter P = 1; endmodule\n"
      "module m; child c(); defparam c.P 5; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(DeclarationAssignmentParsing, PulseControlSpecparamMissingParensIsError) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$ = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
