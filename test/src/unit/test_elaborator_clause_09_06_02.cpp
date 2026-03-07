#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §9.6.2: Disable named block elaborates.
TEST(ElabClause09_06_02, DisableNamedBlockElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  initial begin : blk\n"
      "    a = 1;\n"
      "    disable blk;\n"
      "    a = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.6.2: Disable task name elaborates.
TEST(ElabClause09_06_02, DisableTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task my_task;\n"
      "    #10;\n"
      "  endtask\n"
      "  initial begin\n"
      "    disable my_task;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.6.2: Disable from another process targeting a named block elaborates.
TEST(ElabClause09_06_02, DisableFromOtherProcessElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, x;\n"
      "  initial begin : outer\n"
      "    forever @(posedge clk) x = x + 1;\n"
      "  end\n"
      "  initial begin\n"
      "    #100;\n"
      "    disable outer;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->processes.size(), 2u);
}

// §9.6.2: Disable with conditional guard elaborates.
TEST(ElabClause09_06_02, DisableConditionalElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  initial begin : blk\n"
      "    a = 1;\n"
      "    if (a == 0)\n"
      "      disable blk;\n"
      "    a = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.6.2: Disable in always block elaborates.
TEST(ElabClause09_06_02, DisableInAlwaysElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, q;\n"
      "  always begin : monostable\n"
      "    #250 q = 0;\n"
      "  end\n"
      "  always @(posedge clk) begin\n"
      "    disable monostable;\n"
      "    q = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
