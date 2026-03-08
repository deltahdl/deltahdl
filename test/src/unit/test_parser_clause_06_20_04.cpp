#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserClause03, Cl3_13_ParameterAndLocalparamInModule) {
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

TEST(ParserSection8, ClassWithLocalparam) {
  auto r = Parse(
      "class my_cls;\n"
      "  localparam int SIZE = 8;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "my_cls");
}

TEST(ParserA24, LocalparamAssignment) {
  auto r = Parse("module m; localparam int LP = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "LP");
}

TEST(ParserA28, LocalparamInBlock) {
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

TEST(ParserSection6, LocalparamConstant) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  localparam int DEPTH = 16;\n"
              "endmodule\n"));
}

TEST(ParserSection6, LocalparamInHeaderPort) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter int W = 8, localparam int W2 = W * 2)\n"
              "  (input logic [W-1:0] d);\n"
              "endmodule\n"));
}

TEST(ParserSection6, LocalparamInPackage) {
  EXPECT_TRUE(
      ParseOk("package p;\n"
              "  localparam int SIZE = 256;\n"
              "endpackage\n"));
}

TEST(ParserSection6, LocalparamDerivedFromParam) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter int W = 8);\n"
              "  localparam int W2 = W * 2;\n"
              "  localparam int WMAX = (1 << W) - 1;\n"
              "endmodule\n"));
}

}
