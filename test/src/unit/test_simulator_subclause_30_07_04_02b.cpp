#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string NegativePulseDesign(std::string_view extra_specify_item) {
  std::string source = "module t(input in, output out);\n";
  source += "  logic s;\n";
  source += "  assign in = s;\n";
  source += "  assign out = in;\n";
  source += "  specify\n";
  source += extra_specify_item;
  source += "    (in => out) = (8, 12);\n";
  source += "  endspecify\n";
  source += "  initial begin\n";
  source += "    s = 1'b1;\n";
  source += "    #20 s = 1'b0;\n";
  source += "    #2 s = 1'b1;\n";
  source += "  end\n";
  source += "  initial #25 $display(\"at25=%b\", out);\n";
  source += "  initial #31 $display(\"at31=%b\", out);\n";
  source += "  initial #40 $display(\"at40=%b\", out);\n";
  source += "endmodule\n";
  return source;
}

TEST(NegativePulseAtOutput, DefaultModeShowsNothingOfTheNegativePulse) {
  SimFixture f;
  std::string out = RunCapture(NegativePulseDesign(""), f);
  EXPECT_EQ(out, "at25=1\nat31=1\nat40=1\n");
}

TEST(NegativePulseAtOutput, ExplicitNoshowcancelledShowsNothingEither) {
  SimFixture f;
  std::string out =
      RunCapture(NegativePulseDesign("    noshowcancelled out;\n"), f);
  EXPECT_EQ(out, "at25=1\nat31=1\nat40=1\n");
}

TEST(NegativePulseAtOutput, ShowcancelledOnEventDrivesXFromLeadingSchedule) {
  SimFixture f;
  std::string out =
      RunCapture(NegativePulseDesign("    showcancelled out;\n"), f);
  EXPECT_EQ(out, "at25=1\nat31=x\nat40=1\n");
}

TEST(NegativePulseAtOutput, ShowcancelledOnDetectDrivesXFromDetection) {
  SimFixture f;
  std::string out =
      RunCapture(NegativePulseDesign("    showcancelled out;\n"
                                     "    pulsestyle_ondetect out;\n"),
                 f);
  EXPECT_EQ(out, "at25=x\nat31=x\nat40=1\n");
}

TEST(NegativePulseAtOutput, ListFormDeclarationsApplyToEachOutput) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module mypair(input a, input b, output out, output out_b);\n"
                 "  assign out = a;\n"
                 "  assign out_b = b;\n"
                 "  specify\n"
                 "    showcancelled out, out_b;\n"
                 "    pulsestyle_ondetect out, out_b;\n"
                 "    (a => out) = (4, 6);\n"
                 "    (b => out_b) = (4, 7);\n"
                 "  endspecify\n"
                 "endmodule\n"
                 "module top;\n"
                 "  logic a, b;\n"
                 "  wire t1, t2;\n"
                 "  mypair u(.a(a), .b(b), .out(t1), .out_b(t2));\n"
                 "  always @(t1) if ($time > 8)\n"
                 "    $display(\"t=%0t out=%b\", $time, t1);\n"
                 "  always @(t2) if ($time > 8)\n"
                 "    $display(\"t=%0t out_b=%b\", $time, t2);\n"
                 "  initial begin\n"
                 "    a = 1; b = 1;\n"
                 "    #10 a = 0;\n"
                 "    #1 a = 1;\n"
                 "    #19 b = 0;\n"
                 "    #1 b = 1;\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "t=11 out=x\nt=16 out=1\nt=31 out_b=x\nt=37 out_b=1\n");
}

TEST(NegativePulseAtOutput, TransitionsAfterARejectedStartupPulsePropagate) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module mybuf(input a, output y);\n"
                       "  assign y = a;\n"
                       "  specify\n"
                       "    (a => y) = (5, 12);\n"
                       "  endspecify\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic a; wire ty;\n"
                       "  mybuf u(.a(a), .y(ty));\n"
                       "  always @(ty) if ($time >= 8) $display(\"t=%0t "
                       "y=%b\", $time, ty);\n"
                       "  initial begin\n"
                       "    a = 0;\n"
                       "    #10 a = 1'bx;\n"
                       "    #10 a = 0;\n"
                       "    #30 a = 1;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t=32 y=0\nt=55 y=1\n");
}

}  // namespace
