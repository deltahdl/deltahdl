#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(LocalparamParsing, ParameterAndLocalparamInModule) {
  auto r = Parse(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "  localparam int DEPTH = 16;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  bool found_param = false;
  bool found_localparam = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kParamDecl && item->name == "WIDTH")
      found_param = true;
    if (item->kind == ModuleItemKind::kParamDecl && item->name == "DEPTH")
      found_localparam = true;
  }
  EXPECT_TRUE(found_param);
  EXPECT_TRUE(found_localparam);
}

TEST(LocalparamParsing, ClassWithLocalparam) {
  auto r = Parse(
      "class my_cls;\n"
      "  localparam int SIZE = 8;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "my_cls");
}

TEST(LocalparamParsing, LocalparamAssignment) {
  auto r = Parse("module m; localparam int LP = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "LP");
}

TEST(LocalparamParsing, LocalparamInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    localparam int X = 5;\n"
      "    $display(\"%0d\", X);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_name, "X");
}

TEST(LocalparamParsing, BasicLocalparamParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  localparam int DEPTH = 16;\n"
              "endmodule\n"));
}

TEST(LocalparamParsing, LocalparamInHeaderPort) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter int W = 8, localparam int W2 = W * 2)\n"
              "  (input logic [W-1:0] d);\n"
              "endmodule\n"));
}

TEST(LocalparamParsing, LocalparamInPackage) {
  EXPECT_TRUE(
      ParseOk("package p;\n"
              "  localparam int SIZE = 256;\n"
              "endpackage\n"));
}

TEST(LocalparamParsing, LocalparamDerivedFromParam) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter int W = 8);\n"
              "  localparam int W2 = W * 2;\n"
              "  localparam int WMAX = (1 << W) - 1;\n"
              "endmodule\n"));
}

TEST(LocalparamParsing, LocalparamExplicitType) {
  auto r = Parse("module m; localparam int X = 5; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_TRUE(item->is_localparam);
  EXPECT_EQ(item->name, "X");
}

TEST(LocalparamParsing, LocalparamImplicitType) {
  auto r = Parse("module m; localparam X = 42; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "X");
}

TEST(LocalparamParsing, LocalparamWithPackedDimension) {
  auto r = Parse("module m; localparam [7:0] MASK = 8'hFF; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
}

TEST(LocalparamParsing, ListOfLocalparamAssignments) {
  auto r = Parse("module m; localparam int X = 10, Y = 20; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int param_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) param_count++;
  }
  EXPECT_GE(param_count, 2);
}

TEST(LocalparamParsing, LocalparamReferencesParameter) {
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

TEST(LocalparamParsing, LocalparamInGenerateBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  generate\n"
              "    localparam int X = 3;\n"
              "  endgenerate\n"
              "endmodule\n"));
}

TEST(LocalparamParsing, MixedLocalparamParameterPortList) {
  auto r = Parse(
      "module m #(parameter int A = 1, localparam int B = A * 2,\n"
      "           parameter int C = 3)\n"
      "  ();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->params.size(), 3u);
}

TEST(LocalparamParsing, LocalparamSignedType) {
  auto r = Parse("module m; localparam signed [3:0] N = 4'sb1111; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_TRUE(item->is_localparam);
}

}  // namespace
