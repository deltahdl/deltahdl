#include "fixture_elaborator.h"

namespace {

// §3.1: Design elements are containers for declarations and procedural code.
// The elaborator must accept each design element kind as a valid container.

TEST(ElabClause03, Cl3_1_ModuleAsContainer) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a;\n"
             "  wire b;\n"
             "  assign b = a;\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_1_ModuleWithProceduralBlock) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk, d, q;\n"
             "  always_ff @(posedge clk) q <= d;\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_1_ModuleWithSubroutine) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function int add(int a, int b);\n"
             "    return a + b;\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_1_ModuleWithPorts) {
  EXPECT_TRUE(
      ElabOk("module m(input logic a, output logic b);\n"
             "  assign b = a;\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_1_EmptyModuleElaborates) {
  EXPECT_TRUE(ElabOk("module m; endmodule\n"));
}

}  // namespace
