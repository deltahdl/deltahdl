#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(DataObjectSim, ParameterVariableAndNetEachHoldAValueOfTheirType) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  typedef logic [3:0] nib_t;\n"
      "  parameter nib_t P = 5'h19;\n"
      "  nib_t v = 5'h15;\n"
      "  wire nib_t w = 5'h1a;\n"
      "  initial #1 $display(\"%h %h %h %0d %0d %0d\", P, v, w, $bits(P),\n"
      "                      $bits(v), $bits(w));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "9 5 a 4 4 4\n");
}

TEST(DataObjectSim, TypeBuiltFromAnotherTypeDeclaresObjects) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  typedef logic [3:0] nib_t;\n"
      "  typedef nib_t pair_t [2];\n"
      "  pair_t pr = '{5'h11, 5'h12};\n"
      "  initial #1 $display(\"%h %h %0d\", pr[0], pr[1], $bits(pr));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 2 8\n");
}

}  // namespace
