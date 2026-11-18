#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

TEST(UnnamedGenerateBlockNameSim, DISABLED_PercentMPrintsTheGenblkName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  if (1) begin initial #1 $display(\"%m\"); end\n"
                       "  for (genvar i = 0; i < 2; i++) begin\n"
                       "    initial #(2 + i) $display(\"%m\");\n"
                       "  end\n"
                       "  case (1) 1: begin initial #4 $display(\"%m\"); end "
                       "endcase\n"
                       "  for (genvar j = 0; j < 1; j++)\n"
                       "    initial #5 $display(\"%m\");\n"
                       "endmodule\n",
                       f),
            "top.genblk1\ntop.genblk2[0]\ntop.genblk2[1]\ntop.genblk3\n"
            "top.genblk4[0]\n");
}

TEST(UnnamedGenerateBlockNameSim, DISABLED_PercentMPrintsALeadingZeroName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  logic genblk1;\n"
                       "  if (1) begin initial $display(\"%m\"); end\n"
                       "endmodule\n",
                       f),
            "top.genblk01\n");
}

TEST(UnnamedGenerateBlockNameSim, DISABLED_PercentMPrintsInEachElement) {
  for (const std::string& element : {"interface", "program"}) {
    std::string src = element;
    src +=
        " e;\n"
        "  if (0) begin end\n"
        "  if (1) begin initial $display(\"%m\"); end\n"
        "end";
    src += element;
    src += "\nmodule top;\n  e u();\nendmodule\n";
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f), "top.u.genblk2\n") << element;
  }
}

class UnnamedGenerateBlockVpi : public VpiDesignRun {};

TEST_F(UnnamedGenerateBlockVpi, AGenScopeIsNamedGenblk) {
  Run("module top;\n"
      "  if (1) begin wire a; end\n"
      "  for (genvar i = 0; i < 2; i++) begin wire b; end\n"
      "endmodule\n");
  vpiHandle cond = By("top.genblk1");
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(std::string(vpi_get_str(vpiName, cond)), "genblk1");
  vpiHandle loop = By("top.genblk2[1]");
  ASSERT_NE(loop, nullptr);
  EXPECT_EQ(std::string(vpi_get_str(vpiName, loop)), "genblk2[1]");
}

}  // namespace
