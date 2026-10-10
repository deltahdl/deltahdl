#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"

using namespace delta;

namespace {

// §3.14.2.3 (printed page 60): a program's own timeunit and timeprecision
// stand ahead of the `timescale before it, so under a file-level 1ps / 1ps the
// program's #1.5 is 1.5 of its nanoseconds, kept to its 1 ps precision, and
// its $realtime reads 1.5. Taken in the file's 1 ps it rounded to 2.
TEST(TimescalePrecedenceSimulation, ProgramDeclarationsOutrankTheTimescale) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`timescale 1ps/1ps\n"
                                 "module top;\n"
                                 "  p pi();\n"
                                 "endmodule\n"
                                 "program p;\n"
                                 "  timeunit 1ns; timeprecision 1ps;\n"
                                 "  initial begin\n"
                                 "    #1.5 $display(\"prog t=%0.1f\", "
                                 "$realtime);\n"
                                 "  end\n"
                                 "endprogram\n",
                                 f),
            "prog t=1.5\n");
}

// §3.14.2.2 makes a package a time scope, and §3.14.2.3 b) gives one that
// declares no timeunit the `timescale before its header, so p's #1 is a
// microsecond, which t reads in its own nanoseconds as 1000. The package had
// no scope of its own and its task ran in t's unit, reading 1.
TEST(TimescalePrecedenceSimulation, PackageTakesTheTimescaleBeforeIt) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`timescale 1us / 1ns\n"
                                 "package p;\n"
                                 "  task automatic wait_one(); #1; endtask\n"
                                 "endpackage\n"
                                 "`timescale 1ns / 1ns\n"
                                 "module t;\n"
                                 "  initial begin\n"
                                 "    p::wait_one();\n"
                                 "    $display(\"%0d\", $time);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f),
            "1000\n");
}

// A package that declares only its unit takes its precision by the same
// order, from the `timescale before it: 1 ps here, so its #1.5 is 1.5 ns and
// t reads 1.500. Its precision was taken to be its 1 ns unit, rounding the
// delay to 2.
TEST(TimescalePrecedenceSimulation, PackagePrecisionFollowsTheTimescale) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`timescale 1ns / 1ps\n"
                                 "package p;\n"
                                 "  timeunit 1ns;\n"
                                 "  task automatic wait_frac(); #1.5; endtask\n"
                                 "endpackage\n"
                                 "module t;\n"
                                 "  initial begin\n"
                                 "    p::wait_frac();\n"
                                 "    $display(\"%0.3f\", $realtime);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f),
            "1.500\n");
}

// §3.14.2.3 (printed page 60) a): a module declared inside another (§23.4)
// that specifies no timeunit takes the enclosing module's, ahead of the
// `timescale and the compilation unit's, and its precision by the same order.
// inner's #5 is then 5 us, at top's 3 us after top has printed; run at the
// 1 ns / 1 ns default, it fell to 0 at the 1 us global precision and printed
// first, reading its unit as -9.
TEST(TimescalePrecedenceSimulation, NestedModuleTakesTheEnclosingTimescale) {
  SimFixture f;
  EXPECT_EQ(
      PreprocessAndCapture("`timescale 1us/1us\n"
                           "module top;\n"
                           "  module inner;\n"
                           "    initial begin\n"
                           "      #5 $display(\"inner %0d %0d\", $time, "
                           "$timeunit);\n"
                           "    end\n"
                           "  endmodule\n"
                           "  inner i();\n"
                           "  initial begin #3 $display(\"top %0d\", $time); "
                           "end\n"
                           "endmodule\n",
                           f),
      "top 3\ninner 5 -6\n");
}

TEST(TimescalePrecedenceSimulation, NestedModuleTakesTheEnclosingTimeunit) {
  SimFixture f;
  EXPECT_EQ(
      PreprocessAndCapture("module top;\n"
                           "  timeunit 1us; timeprecision 1us;\n"
                           "  module inner;\n"
                           "    initial begin\n"
                           "      #5 $display(\"inner %0d %0d\", $time, "
                           "$timeunit);\n"
                           "    end\n"
                           "  endmodule\n"
                           "  inner i();\n"
                           "  initial begin #3 $display(\"top %0d\", $time); "
                           "end\n"
                           "endmodule\n",
                           f),
      "top 3\ninner 5 -6\n");
}

}  // namespace
