#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"

using namespace delta;

namespace {

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

TEST(TimescalePrecedenceSimulation,
     InterfaceNestedInAnInterfaceTakesItsTimeunit) {
  SimFixture f;
  EXPECT_EQ(
      PreprocessAndCapture("interface bus;\n"
                           "  timeunit 1us; timeprecision 1us;\n"
                           "  interface inner;\n"
                           "    initial begin\n"
                           "      #5 $display(\"inner %0d %0d\", $time, "
                           "$timeunit);\n"
                           "    end\n"
                           "  endinterface\n"
                           "  inner i();\n"
                           "endinterface\n"
                           "module top;\n"
                           "  timeunit 1ns; timeprecision 1ns;\n"
                           "  bus b();\n"
                           "  initial begin #3 $display(\"top %0d\", $time); "
                           "end\n"
                           "endmodule\n",
                           f),
      "top 3\ninner 5 -6\n");
}

TEST(TimescalePrecedenceSimulation, InterfaceNestedInAModuleTakesItsTimeunit) {
  SimFixture f;
  EXPECT_EQ(
      PreprocessAndCapture("`timescale 1ns/1ns\n"
                           "module top;\n"
                           "  timeunit 1us; timeprecision 1us;\n"
                           "  interface inner;\n"
                           "    initial begin\n"
                           "      #5 $display(\"inner %0d %0d\", $time, "
                           "$timeunit);\n"
                           "    end\n"
                           "  endinterface\n"
                           "  inner i();\n"
                           "  initial begin #3 $display(\"top %0d\", $time); "
                           "end\n"
                           "endmodule\n",
                           f),
      "top 3\ninner 5 -6\n");
}

}  // namespace
