#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

struct TwoUnconditionalPathsCase {
  std::string_view driver;
  std::string_view stimulus;
  int early;
  int late;
};

std::string TwoUnconditionalPathsSource(const TwoUnconditionalPathsCase& tc) {
  std::string early = std::to_string(tc.early);
  std::string late = std::to_string(tc.late);
  std::string src = "module top(input a, b, output y);\n";
  src += "  logic sa, sb, armed;\n";
  src += "  assign a = sa;\n";
  src += "  assign b = sb;\n";
  src += "  assign y = ";
  src += tc.driver;
  src += ";\n";
  src += "  specify\n";
  src += "    (a => y) = (6, 9);\n";
  src += "    (b => y) = (5, 11);\n";
  src += "  endspecify\n";
  src += "  initial begin\n";
  src += "    armed = 1'b0;\n";
  src += tc.stimulus;
  src += "  end\n";
  src += "  always @(y) begin\n";
  src += "    if (armed) $display(\"y=%b@%0d\", y, $time);\n";
  src += "  end\n";
  src += "  initial #" + early + " $display(\"s" + early + "=%b\", y);\n";
  src += "  initial #" + late + " $display(\"s" + late + "=%b\", y);\n";
  src += "endmodule\n";
  return src;
}

TEST(ActiveModulePathSelection, RiseTakesTheRiseDelayOfTheLaterInputA) {
  SimFixture f;
  std::string out =
      RunCapture(TwoUnconditionalPathsSource({"a & b",
                                              "    sa = 1'b0;\n"
                                              "    sb = 1'b0;\n"
                                              "    #20 sb = 1'b1;\n"
                                              "    #20 armed = 1'b1;\n"
                                              "    #10 sa = 1'b1;\n",
                                              54, 58}),
                 f);
  EXPECT_EQ(out, "s54=0\ny=1@56\ns58=1\n");
}

TEST(ActiveModulePathSelection, RiseTakesTheRiseDelayOfTheLaterInputB) {
  SimFixture f;
  std::string out =
      RunCapture(TwoUnconditionalPathsSource({"a & b",
                                              "    sa = 1'b0;\n"
                                              "    sb = 1'b0;\n"
                                              "    #20 sa = 1'b1;\n"
                                              "    #20 armed = 1'b1;\n"
                                              "    #10 sb = 1'b1;\n",
                                              54, 58}),
                 f);
  EXPECT_EQ(out, "s54=0\ny=1@55\ns58=1\n");
}

TEST(ActiveModulePathSelection, SimultaneousInputsRiseOnTheSmallerDelay) {
  SimFixture f;
  std::string out =
      RunCapture(TwoUnconditionalPathsSource({"a & b",
                                              "    sa = 1'b0;\n"
                                              "    sb = 1'b0;\n"
                                              "    #40 armed = 1'b1;\n"
                                              "    #10 sa = 1'b1;\n"
                                              "    sb = 1'b1;\n",
                                              54, 58}),
                 f);
  EXPECT_EQ(out, "s54=0\ny=1@55\ns58=1\n");
}

TEST(ActiveModulePathSelection, FallTakesTheFallDelayOfTheLaterInputA) {
  SimFixture f;
  std::string out =
      RunCapture(TwoUnconditionalPathsSource({"a | b",
                                              "    sa = 1'b1;\n"
                                              "    sb = 1'b1;\n"
                                              "    #40 armed = 1'b1;\n"
                                              "    #10 sb = 1'b0;\n"
                                              "    #10 sa = 1'b0;\n",
                                              65, 73}),
                 f);
  EXPECT_EQ(out, "s65=1\ny=0@69\ns73=0\n");
}

std::string TwoPathGate(const std::string& paths) {
  return "module mygate(input clk, input data, output q);\n"
         "  assign q = clk & data;\n"
         "  specify\n" +
         paths +
         "  endspecify\n"
         "endmodule\n"
         "module top;\n"
         "  logic clk, data;\n"
         "  wire tq;\n"
         "  mygate u(.clk(clk), .data(data), .q(tq));\n"
         "  always @(tq) if ($time >= 20) $display(\"t=%0t q=%b\", $time, "
         "tq);\n"
         "  initial begin\n"
         "    clk = 0; data = 1;\n"
         "    #30 clk = 1;\n"
         "    #30 clk = 0;\n"
         "  end\n"
         "endmodule\n";
}

TEST(ActivePathSelectionRun, SameTerminalPathsAreBothKept) {
  SimFixture f;
  EXPECT_EQ(RunCapture(TwoPathGate("    (clk => q) = (10, 5);\n"
                                   "    (clk => q) = (20, 6);\n"),
                       f),
            "t=40 q=1\nt=65 q=0\n");
}

TEST(ActivePathSelectionRun, EachTransitionTakesItsOwnSmallestDelay) {
  SimFixture f;
  EXPECT_EQ(RunCapture(TwoPathGate("    (clk => q) = (10, 6);\n"
                                   "    (clk => q) = (20, 5);\n"),
                       f),
            "t=40 q=1\nt=65 q=0\n");
}

TEST(ActiveModulePathSelection,
     SimultaneousInputsInOneStepTakeTheSmallerDelay) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module myor(input a, input b, output y);\n"
                       "  assign y = a | b;\n"
                       "  specify\n"
                       "    (a => y) = (6, 9);\n"
                       "    (b => y) = (5, 11);\n"
                       "  endspecify\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic a, b; wire ty;\n"
                       "  myor u(.a(a), .b(b), .y(ty));\n"
                       "  always @(ty) if ($time >= 10) $display(\"t=%0t "
                       "y=%b\", $time, ty);\n"
                       "  initial begin\n"
                       "    a = 0; b = 0;\n"
                       "    #10 begin a = 1; b = 1; end\n"
                       "    #10 begin a = 0; b = 0; end\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t=15 y=1\nt=29 y=0\n");
}

}  // namespace
