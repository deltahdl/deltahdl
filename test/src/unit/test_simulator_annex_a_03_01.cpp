#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(NInputGateRun, ASingleInputGateOfEachTypeDrivesItsOwnFunction) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  logic i;\n"
      "  wire oa, on, oo, or_n, ox, oxn;\n"
      "  and g1 (oa, i);\n"
      "  nand g2 (on, i);\n"
      "  or g3 (oo, i);\n"
      "  nor g4 (or_n, i);\n"
      "  xor g5 (ox, i);\n"
      "  xnor g6 (oxn, i);\n"
      "  initial begin\n"
      "    i = 1'b0;\n"
      "    #1 $display(\"%b%b%b%b%b%b\", oa, on, oo, or_n, ox, oxn);\n"
      "    i = 1'b1;\n"
      "    #1 $display(\"%b%b%b%b%b%b\", oa, on, oo, or_n, ox, oxn);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "010101\n101010\n");
}

}  // namespace
