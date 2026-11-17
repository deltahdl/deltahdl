#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(MultiInstanceStatement, EachInstanceIsBoundToItsOwnConnections) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub(input a);\n"
                       "  initial #1 $display(\"%m %b\", a);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  wire a = 1, b = 0;\n"
                       "  sub u1(a), u2(b);\n"
                       "endmodule\n",
                       f),
            "t.u1 1\nt.u2 0\n");
}

TEST(MultiInstanceStatement, OneInstanceOrderedAndAnotherNamedAreAccepted) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module c(input a, b);\n"
                       "  initial #1 $display(\"%m %b %b\", a, b);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  wire x = 1, y = 0, z = 1;\n"
                       "  c u1(x, y), u2(.a(x), .b(z));\n"
                       "endmodule\n",
                       f),
            "t.u1 1 0\nt.u2 1 1\n");
}

TEST(MultiInstanceStatement, TheFlipFlopTripleTakesEachInstancesNamedList) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module ffnand(output q, qbar, input clear, preset);\n"
                 "  assign q = preset;\n"
                 "  assign qbar = clear;\n"
                 "endmodule\n"
                 "module t;\n"
                 "  wire out1, out2, out3;\n"
                 "  wire in1 = 1, in2 = 0;\n"
                 "  ffnand ff1(.q(), .qbar(out1), .clear(in1), .preset(in2)),\n"
                 "         ff2(.q(), .qbar(out2), .clear(in2), .preset(in1)),\n"
                 "         ff3(.q(out3), .qbar(), .clear(in1), .preset(in2));\n"
                 "  initial #1 $display(\"%b %b %b\", out1, out2, out3);\n"
                 "endmodule\n",
                 f),
      "1 0 0\n");
}

}  // namespace
