#include "helpers_preprocess_and_get.h"

// §22.10 (C5) states that `celldefine and `endcelldefine may appear anywhere
// in the source description. "Anywhere" includes positions the other Clause 22
// state directives reject -- inside a design element, and inside a procedural
// block
// -- so the runtime consequence of the rule is that the surrounding design is
// untouched: it still elaborates, still lowers, and still computes the same
// values it would compute with the directives removed.
//
// The tag the directives apply is a compile-time property of a module; it does
// not reach the simulator, so what is checked here is that placing the
// directives in each permitted position leaves behaviour alone.

TEST(CelldefineSimulation, CellModuleRunsUnchanged) {
  auto result = PreprocessAndGet(
      "`celldefine\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd42;\n"
      "endmodule\n"
      "`endcelldefine\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(CelldefineSimulation, DirectivesInsideModuleBodyRunUnchanged) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "`celldefine\n"
      "  logic [7:0] result;\n"
      "`endcelldefine\n"
      "  initial result = 8'd17;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 17u);
}

// C6: `resetall carries the effect of an `endcelldefine. The directive it
// depends on is written here in its real §22.3 form and driven through the
// whole pipeline, so what is checked is that ending a cell region this way
// leaves the modules on both sides of it running normally.
TEST(CelldefineSimulation, ResetallBetweenModulesRunsUnchanged) {
  auto result = PreprocessAndGet(
      "`celldefine\n"
      "module cell_mod;\n"
      "  logic [7:0] spare;\n"
      "  initial spare = 8'd1;\n"
      "endmodule\n"
      "`resetall\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd21 + 8'd21;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(CelldefineSimulation, DirectivesInsideProceduralBlockRunUnchanged) {
  auto result = PreprocessAndGet(
      "`celldefine\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "`endcelldefine\n"
      "    result = 8'd5;\n"
      "    result = result + 8'd3;\n"
      "`celldefine\n"
      "  end\n"
      "endmodule\n"
      "`endcelldefine\n",
      "result");
  EXPECT_EQ(result, 8u);
}
