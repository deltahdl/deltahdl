#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr std::string_view kPulseStimulus =
    "    s = 1'b1;\n"
    "    #20 s = 1'b0;\n"
    "    #4 s = 1'b1;\n";

constexpr std::string_view kNoPulseStimulus =
    "    s = 1'b1;\n"
    "    #20 s = 1'b0;\n"
    "    #20 s = 1'b1;\n";

std::string PulseDesign(std::string_view extra_specify_item,
                        std::string_view stimulus, int first_sample,
                        int second_sample) {
  std::string first = std::to_string(first_sample);
  std::string second = std::to_string(second_sample);
  return std::string(
             "module t(input a, output y);\n"
             "  logic s;\n"
             "  assign a = s;\n"
             "  assign y = a;\n"
             "  specify\n"
             "    (a => y) = (7, 9);\n") +
         std::string(extra_specify_item) +
         "  endspecify\n"
         "  initial begin\n" +
         std::string(stimulus) +
         "  end\n"
         "  initial #" +
         first + " $display(\"at" + first + "=%b\", y);\n" + "  initial #" +
         second + " $display(\"at" + second + "=%b\", y);\n" + "endmodule\n";
}

TEST(ModulePathPulseFiltering, PulseBelowRejectLimitNeverReachesOutput) {
  SimFixture f;
  std::string out = RunCapture(PulseDesign("", kPulseStimulus, 30, 35), f);
  EXPECT_EQ(out, "at30=1\nat35=1\n");
}

TEST(ModulePathPulseFiltering, TransitionsWiderThanDelayAreNotAPulse) {
  SimFixture f;
  std::string out = RunCapture(PulseDesign("", kNoPulseStimulus, 35, 50), f);
  EXPECT_EQ(out, "at35=0\nat50=1\n");
}

TEST(ModulePathPulseFiltering, PulseAtRejectLimitBelowErrorLimitDrivesX) {
  SimFixture f;
  std::string out =
      RunCapture(PulseDesign("    specparam PATHPULSE$a$y = (2, 9);\n",
                             kPulseStimulus, 30, 35),
                 f);
  EXPECT_EQ(out, "at30=x\nat35=1\n");
}

TEST(ModulePathPulseFiltering, PulseAtErrorLimitPropagatesToOutput) {
  SimFixture f;
  std::string out =
      RunCapture(PulseDesign("    specparam PATHPULSE$a$y = (2, 2);\n",
                             kPulseStimulus, 30, 35),
                 f);
  EXPECT_EQ(out, "at30=0\nat35=1\n");
}

TEST(ModulePathPulseFiltering, SamePulseIsRejectedByNarrowerLimit) {
  SimFixture f;
  std::string out =
      RunCapture(PulseDesign("    specparam PATHPULSE$a$y = (3, 3);\n",
                             kPulseStimulus, 30, 35),
                 f);
  EXPECT_EQ(out, "at30=1\nat35=1\n");
}

TEST(ModulePathPulseFiltering, TransitionsAfterARejectedPulseStillPropagate) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module mybuf(input a, output y);\n"
          "  assign y = a;\n"
          "  specify\n"
          "    (a => y) = 7;\n"
          "  endspecify\n"
          "endmodule\n"
          "module top;\n"
          "  logic a; wire ty;\n"
          "  mybuf u(.a(a), .y(ty));\n"
          "  always @(ty) if ($time > 0) $display(\"t=%0t y=%b\", $time, ty);\n"
          "  initial begin\n"
          "    a = 1;\n"
          "    #10 a = 0;\n"
          "    #6 a = 1;\n"
          "    #14 a = 0;\n"
          "    #20 a = 1;\n"
          "  end\n"
          "endmodule\n",
          f),
      "t=7 y=1\nt=37 y=0\nt=57 y=1\n");
}

}  // namespace
