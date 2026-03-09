#include "fixture_elaborator.h"

namespace {

TEST(ElabClause03, Cl3_3_Mux2to1ExampleElaborates) {
  EXPECT_TRUE(
      ElabOk("module mux2to1 (input wire a, b, sel,\n"
             "                output logic y);\n"
             "  always_comb begin\n"
             "    if (sel) y = a;\n"
             "    else     y = b;\n"
             "  end\n"
             "endmodule: mux2to1\n"));
}

TEST(ElabClause03, Cl3_3_Mux2to1HasCorrectPorts) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module mux2to1 (input wire a, b, sel,\n"
      "                output logic y);\n"
      "  always_comb begin\n"
      "    if (sel) y = a;\n"
      "    else     y = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto* top = design->top_modules[0];
  EXPECT_EQ(top->ports.size(), 4u);
}

TEST(ElabClause03, Cl3_3_ModuleWithMixedContents) {
  EXPECT_TRUE(
      ElabOk("module m (input logic clk, output logic [7:0] q);\n"
             "  wire [7:0] net;\n"
             "  logic [7:0] var;\n"
             "  localparam int HALF = 4;\n"
             "  assign net = var;\n"
             "  always_comb var = ~q;\n"
             "  always_ff @(posedge clk) q <= net;\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_3_ModuleWithSubroutineElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function int add(int a, int b);\n"
             "    return a + b;\n"
             "  endfunction\n"
             "  task do_nothing;\n"
             "  endtask\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_3_ModuleWithModuleInstElaborates) {
  EXPECT_TRUE(
      ElabOk("module sub(input logic a, output logic b);\n"
             "  assign b = a;\n"
             "endmodule\n"
             "module top;\n"
             "  logic x, y;\n"
             "  sub u0(.a(x), .b(y));\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_3_ModuleWithGenerateElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter int P = 1;\n"
             "  if (P) begin : gen\n"
             "    logic w;\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
