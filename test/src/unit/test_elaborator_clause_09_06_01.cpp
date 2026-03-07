#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §9.6.1: Wait fork elaborates in an initial block.
TEST(ElabClause09_06_01, WaitForkInInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    fork\n"
      "      #10 a = 1;\n"
      "    join_none\n"
      "    wait fork;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.6.1: Wait fork is a timing control, error in always_comb.
TEST(ElabClause09_06_01, WaitForkInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  always_comb begin\n"
      "    wait fork;\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.6.1: Wait fork is a timing control, error in always_ff.
TEST(ElabClause09_06_01, WaitForkInAlwaysFFErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a;\n"
      "  always_ff @(posedge clk) begin\n"
      "    wait fork;\n"
      "    a <= 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.6.1: Wait fork is a timing control, error in final.
TEST(ElabClause09_06_01, WaitForkInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  final begin\n"
      "    wait fork;\n"
      "    a = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.6.1: Wait fork standalone (no preceding fork) still elaborates.
TEST(ElabClause09_06_01, WaitForkStandaloneElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    wait fork;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
