// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, ModuleWithNetDecl) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kNetDecl);
}

TEST(DesignBuildingBlockParsing, ModuleWithVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kVarDecl);
}

TEST(DesignBuildingBlockParsing, ModuleWithStructDecl) {
  auto r = Parse(
      "module m;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DesignBuildingBlockParsing, ModuleWithUnionDecl) {
  auto r = Parse(
      "module m;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } u;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DesignBuildingBlockParsing, ModuleWithParamDecl) {
  auto r = Parse(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "  localparam int DEPTH = 4;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int param_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) param_count++;
  }
  EXPECT_EQ(param_count, 2);
}

TEST(DesignBuildingBlockParsing, ModuleWithTypedef) {
  auto r = Parse(
      "module m;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  byte_t data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kTypedef);
}

TEST(DesignBuildingBlockParsing, ModuleWithClassDecl) {
  auto r = Parse(
      "module m;\n"
      "  class C;\n"
      "    int x;\n"
      "  endclass\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kClassDecl);
}

TEST(DesignBuildingBlockParsing, ModuleWithImport) {
  auto r = Parse(
      "package pkg; typedef int myint; endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kImportDecl);
}

TEST(DesignBuildingBlockParsing, ModuleWithFunction) {
  auto r = Parse(
      "module m;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kFunctionDecl);
}

TEST(DesignBuildingBlockParsing, ModuleWithTask) {
  auto r = Parse(
      "module m;\n"
      "  task do_nothing;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kTaskDecl);
}

TEST(DesignBuildingBlockParsing, ModuleWithModuleInst) {
  auto r = Parse(
      "module sub; endmodule\n"
      "module m;\n"
      "  sub u0();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[1]->items[0]->kind, ModuleItemKind::kModuleInst);
}

TEST(DesignBuildingBlockParsing, ModuleWithGateInst) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, y;\n"
      "  nand g1(y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool has_gate = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGateInst) has_gate = true;
  }
  EXPECT_TRUE(has_gate);
}

TEST(DesignBuildingBlockParsing, ModuleWithContAssign) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign b = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool has_assign = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) has_assign = true;
  }
  EXPECT_TRUE(has_assign);
}

TEST(DesignBuildingBlockParsing, ModuleWithInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  initial a = 0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[1]->kind, ModuleItemKind::kInitialBlock);
}

TEST(DesignBuildingBlockParsing, ModuleWithFinalBlock) {
  auto r = Parse(
      "module m;\n"
      "  final $display(\"done\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kFinalBlock);
}

TEST(DesignBuildingBlockParsing, ModuleWithAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic clk, q, d;\n"
              "  always @(posedge clk) q <= d;\n"
              "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, ModuleWithAlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb y = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[2]->kind, ModuleItemKind::kAlwaysCombBlock);
}

TEST(DesignBuildingBlockParsing, ModuleWithAlwaysFF) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic clk, d, q;\n"
              "  always_ff @(posedge clk) q <= d;\n"
              "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, ModuleWithAlwaysLatch) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic en, d, q;\n"
              "  always_latch if (en) q <= d;\n"
              "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, ModuleWithGenerateFor) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  genvar i;\n"
              "  for (i = 0; i < 4; i = i + 1) begin : gen\n"
              "    wire w;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, ModuleWithGenerateIf) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter int P = 1;\n"
              "  if (P) begin : gen\n"
              "    wire w;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, ModuleWithSpecifyBlock) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  assign y = a;\n"
      "  specify\n"
      "    (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool has_specify = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) has_specify = true;
  }
  EXPECT_TRUE(has_specify);
}

TEST(DesignBuildingBlockParsing, Mux2to1Example) {
  auto r = Parse(
      "module mux2to1 (input wire a, b, sel,\n"
      "                output logic y);\n"
      "  always_comb begin\n"
      "    if (sel) y = a;\n"
      "    else     y = b;\n"
      "  end\n"
      "endmodule: mux2to1\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "mux2to1");
  EXPECT_FALSE(r.cu->modules[0]->ports.empty());
  EXPECT_FALSE(r.cu->modules[0]->items.empty());
}

TEST(DesignBuildingBlockParsing, ModuleWithMixedContents) {
  EXPECT_TRUE(ParseOk(
      "module m #(parameter int W = 8) (input logic clk, output logic [W-1:0] "
      "q);\n"
      "  typedef logic [W-1:0] data_t;\n"
      "  wire [W-1:0] net;\n"
      "  logic [W-1:0] var;\n"
      "  localparam int HALF = W / 2;\n"
      "  function automatic data_t invert(data_t d); return ~d; endfunction\n"
      "  assign net = var;\n"
      "  always_comb var = invert(q);\n"
      "  always_ff @(posedge clk) q <= net;\n"
      "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, MultipleModulesInOneCU) {
  auto r = Parse(
      "module a; endmodule\nmodule b; endmodule\n"
      "module c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
  EXPECT_EQ(r.cu->modules[2]->name, "c");
}

TEST(DesignBuildingBlockParsing, MismatchedEndKeywordIsError) {
  EXPECT_FALSE(ParseOk("module m; endprogram"));
}

TEST(DesignBuildingBlockParsing, UnclosedModuleIsError) {
  EXPECT_FALSE(ParseOk("module m;"));
}

}  // namespace
