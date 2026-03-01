// §3.3: Modules

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §3.3 LRM mux2to1 example (verbatim, with always_comb procedural block).
TEST(ParserClause03, Cl3_3_Mux2to1LrmExample) {
  auto r = ParseWithPreprocessor(
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
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 4u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[3].name, "y");
  auto* blk = FindItemByKind(r, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(blk, nullptr);
  EXPECT_EQ(blk->always_kind, AlwaysKind::kAlwaysComb);
}

// §3.3 Data declarations, constants, user-defined types, class definitions
TEST(ParserClause03, Cl3_3_ModuleDeclarations) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire [7:0] w;\n"
      "  logic [15:0] v;\n"
      "  struct packed { logic [3:0] a; logic [3:0] b; } s;\n"
      "  union packed { logic [7:0] x; logic [7:0] y; } u;\n"
      "  parameter WIDTH = 8;\n"
      "  localparam DEPTH = 16;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  class my_class; int val; endclass\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kParamDecl));
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kTypedef));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kClassDecl));
  EXPECT_GE(r.cu->modules[0]->items.size(), 7u);
}

// §3.3 Subroutine definitions and procedural blocks
TEST(ParserClause03, Cl3_3_SubroutinesAndProceduralBlocks) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  function int add(int a, int b); return a + b; endfunction\n"
      "  task display_val(input int x); $display(\"%d\", x); endtask\n"
      "  initial a = 0;\n"
      "  final $display(\"done\");\n"
      "  always @(posedge clk) a <= b;\n"
      "  always_comb b = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kFunctionDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kTaskDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kFinalBlock));
  EXPECT_TRUE(HasAlwaysOfKind(r.cu->modules[0]->items, AlwaysKind::kAlways));
  EXPECT_TRUE(
      HasAlwaysOfKind(r.cu->modules[0]->items, AlwaysKind::kAlwaysComb));
}

}  // namespace
