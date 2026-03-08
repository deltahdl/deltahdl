#include "fixture_parser.h"

using namespace delta;

namespace {

// §3.3: A module is enclosed between module...endmodule and can contain
// the constructs enumerated in this clause.

// --- Ports ---

TEST(ParserClause03, Cl3_3_ModuleWithPortDeclarations) {
  auto r = Parse(
      "module m(input wire a, b, sel, output logic y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.cu->modules[0]->ports.empty());
}

// --- Data declarations (nets, variables, structures, unions) ---

TEST(ParserClause03, Cl3_3_ModuleWithNetDecl) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kNetDecl);
}

TEST(ParserClause03, Cl3_3_ModuleWithVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kVarDecl);
}

TEST(ParserClause03, Cl3_3_ModuleWithStructDecl) {
  auto r = Parse(
      "module m;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserClause03, Cl3_3_ModuleWithUnionDecl) {
  auto r = Parse(
      "module m;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } u;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- Constant declarations ---

TEST(ParserClause03, Cl3_3_ModuleWithParamDecl) {
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

// --- User-defined type definitions ---

TEST(ParserClause03, Cl3_3_ModuleWithTypedef) {
  auto r = Parse(
      "module m;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  byte_t data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kTypedef);
}

// --- Class definitions ---

TEST(ParserClause03, Cl3_3_ModuleWithClassDecl) {
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

// --- Imports of declarations from packages ---

TEST(ParserClause03, Cl3_3_ModuleWithImport) {
  auto r = Parse(
      "package pkg; typedef int myint; endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kImportDecl);
}

// --- Subroutine definitions ---

TEST(ParserClause03, Cl3_3_ModuleWithFunction) {
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

TEST(ParserClause03, Cl3_3_ModuleWithTask) {
  auto r = Parse(
      "module m;\n"
      "  task do_nothing;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kTaskDecl);
}

// --- Instantiations ---

TEST(ParserClause03, Cl3_3_ModuleWithModuleInst) {
  auto r = Parse(
      "module sub; endmodule\n"
      "module m;\n"
      "  sub u0();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[1]->items[0]->kind, ModuleItemKind::kModuleInst);
}

TEST(ParserClause03, Cl3_3_ModuleWithGateInst) {
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

// --- Continuous assignments ---

TEST(ParserClause03, Cl3_3_ModuleWithContAssign) {
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

// --- Procedural blocks ---

TEST(ParserClause03, Cl3_3_ModuleWithInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  initial a = 0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[1]->kind, ModuleItemKind::kInitialBlock);
}

TEST(ParserClause03, Cl3_3_ModuleWithFinalBlock) {
  auto r = Parse(
      "module m;\n"
      "  final $display(\"done\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kFinalBlock);
}

TEST(ParserClause03, Cl3_3_ModuleWithAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic clk, q, d;\n"
              "  always @(posedge clk) q <= d;\n"
              "endmodule\n"));
}

TEST(ParserClause03, Cl3_3_ModuleWithAlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb y = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[2]->kind, ModuleItemKind::kAlwaysCombBlock);
}

TEST(ParserClause03, Cl3_3_ModuleWithAlwaysFF) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic clk, d, q;\n"
              "  always_ff @(posedge clk) q <= d;\n"
              "endmodule\n"));
}

TEST(ParserClause03, Cl3_3_ModuleWithAlwaysLatch) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic en, d, q;\n"
              "  always_latch if (en) q <= d;\n"
              "endmodule\n"));
}

// --- Generate blocks ---

TEST(ParserClause03, Cl3_3_ModuleWithGenerateFor) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  genvar i;\n"
              "  for (i = 0; i < 4; i = i + 1) begin : gen\n"
              "    wire w;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserClause03, Cl3_3_ModuleWithGenerateIf) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter int P = 1;\n"
              "  if (P) begin : gen\n"
              "    wire w;\n"
              "  end\n"
              "endmodule\n"));
}

// --- Specify blocks ---

TEST(ParserClause03, Cl3_3_ModuleWithSpecifyBlock) {
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

// --- LRM §3.3 mux2to1 example ---

TEST(ParserClause03, Cl3_3_Mux2to1Example) {
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

// --- Combined: module with many construct types ---

TEST(ParserClause03, Cl3_3_ModuleWithMixedContents) {
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

}  // namespace
