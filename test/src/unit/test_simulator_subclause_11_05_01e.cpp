// §11.5.1 Vector bit-select and part-select addressing, for a parameter
// initialized from a constant select of another parameter: a select reaching
// outside the 4-state vector reads x for its out-of-range bits, and a
// part-select of 64 bits or more reads every one of them. Constant folding
// leaves the first unfolded (test/src/unit/test_elaborator_subclause_11_05_01d
// .cpp), so these read the value the parameter holds in simulation.

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ParameterSelectSim, OutOfRangeSelectOfAFourStateParameterReadsX) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  parameter logic [7:0] P = 8'hFF;\n"
      "  localparam logic Q = P[9];\n"
      "  localparam logic [3:0] R = P[9:6];\n"
      "  parameter logic [127:0] W = {64'h1, 64'hFFFF_FFFF_FFFF_FFFF};\n"
      "  localparam logic [63:0] L = W[63:0];\n"
      "  initial $display(\"%b %b %h\", Q, R, L);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x xx11 ffffffffffffffff\n");
}

}  // namespace
