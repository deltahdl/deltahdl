#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

constexpr std::string_view kSetupViolation = "$setup violation: data signal";

std::string NotifierDesign(std::string_view initial_value, unsigned limit,
                           unsigned data_time, unsigned interval) {
  return std::string(
             "module top(\n"
             "    output logic d,\n"
             "    output logic clk);\n"
             "  logic setup_notifier;\n"
             "  specify\n"
             "    $setup(d, posedge clk, ") +
         std::to_string(limit) +
         ", setup_notifier);\n"
         "  endspecify\n"
         "  initial begin\n"
         "    setup_notifier = " +
         std::string(initial_value) +
         ";\n"
         "    d = 1'b0;\n"
         "    clk = 1'b0;\n"
         "    #" +
         std::to_string(data_time) + " d = 1'b1;\n    #" +
         std::to_string(interval) +
         " clk = 1'b1;\n"
         "  end\n"
         "endmodule\n";
}

TEST(NotifierUpdateDriven, ZNotifierSurvivesADrivenViolation) {
  SimFixture f;
  const std::string kDesign = NotifierDesign("1'bz", 37, 101, 13);
  auto* notifier = RunAndFindVar(kDesign, f, "setup_notifier");
  ASSERT_NE(notifier, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kSetupViolation,
                              LineHolding(kDesign, "$setup(d, posedge clk,"),
                              "31.3.1"));
  EXPECT_EQ(notifier->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(notifier->value.words[0].bval & 1u, 1u);
}

TEST(NotifierUpdateDriven, XNotifierBecomesKnownAfterADrivenViolation) {
  SimFixture f;
  const std::string kDesign = NotifierDesign("1'bx", 41, 107, 17);
  auto* notifier = RunAndFindVar(kDesign, f, "setup_notifier");
  ASSERT_NE(notifier, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kSetupViolation,
                              LineHolding(kDesign, "$setup(d, posedge clk,"),
                              "31.3.1"));
  EXPECT_EQ(notifier->value.words[0].bval & 1u, 0u);
}

TEST(NotifierUpdateDriven, ZeroNotifierBecomesOneAfterADrivenViolation) {
  SimFixture f;
  const std::string kDesign = NotifierDesign("1'b0", 43, 109, 19);
  auto* notifier = RunAndFindVar(kDesign, f, "setup_notifier");
  ASSERT_NE(notifier, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kSetupViolation,
                              LineHolding(kDesign, "$setup(d, posedge clk,"),
                              "31.3.1"));
  EXPECT_EQ(notifier->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(notifier->value.words[0].bval & 1u, 0u);
}

TEST(NotifierUpdateDriven, OneNotifierBecomesZeroAfterADrivenViolation) {
  SimFixture f;
  const std::string kDesign = NotifierDesign("1'b1", 47, 113, 23);
  auto* notifier = RunAndFindVar(kDesign, f, "setup_notifier");
  ASSERT_NE(notifier, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kSetupViolation,
                              LineHolding(kDesign, "$setup(d, posedge clk,"),
                              "31.3.1"));
  EXPECT_EQ(notifier->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(notifier->value.words[0].bval & 1u, 0u);
}

TEST(NotifierUpdateDriven, SatisfiedWindowLeavesTheDrivenNotifierAtZero) {
  SimFixture f;
  auto* notifier =
      RunAndFindVar(NotifierDesign("1'b0", 29, 127, 31), f, "setup_notifier");
  ASSERT_NE(notifier, nullptr);
  EXPECT_EQ(FindDiag(f, kSetupViolation), nullptr);
  EXPECT_EQ(notifier->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(notifier->value.words[0].bval & 1u, 0u);
}

TEST(NotifierUpdateDriven, FlipFlopGoesToXOnASetupViolation) {
  SimFixture f;
  const std::string kDesign =
      "primitive posdff_udp(q, clock, data, preset, clear, notifier);\n"
      "  output q; reg q;\n"
      "  input clock, data, preset, clear, notifier;\n"
      "  table\n"
      "    r 0 1 1 ? : ? : 0 ;\n"
      "    r 1 1 1 ? : ? : 1 ;\n"
      "    p 1 ? 1 ? : 1 : 1 ;\n"
      "    p 0 1 ? ? : 0 : 0 ;\n"
      "    n ? ? ? ? : ? : - ;\n"
      "    ? * ? ? ? : ? : - ;\n"
      "    ? ? 0 1 ? : ? : 1 ;\n"
      "    ? ? * 1 ? : 1 : 1 ;\n"
      "    ? ? 1 0 ? : ? : 0 ;\n"
      "    ? ? 1 * ? : 0 : 0 ;\n"
      "    ? ? ? ? * : ? : x ;\n"
      "  endtable\n"
      "endprimitive\n"
      "module dff(q, qbar, clock, data, preset, clear);\n"
      "  output q, qbar;\n"
      "  input clock, data, preset, clear;\n"
      "  reg notifier;\n"
      "  and (enable, preset, clear);\n"
      "  not (qbar, ffout);\n"
      "  buf (q, ffout);\n"
      "  posdff_udp (ffout, clock, data, preset, clear, notifier);\n"
      "  specify\n"
      "    specparam tSU = 10, tHD = 1, tPW = 25, tWPC = 10, tREC = 5;\n"
      "    specparam tPLHc = 4:6:9 , tPHLc = 5:8:11;\n"
      "    specparam tPLHpc = 3:5:6 , tPHLpc = 4:7:9;\n"
      "    (clock *> q,qbar) = (tPLHc, tPHLc);\n"
      "    (preset,clear *> q,qbar) = (tPLHpc, tPHLpc);\n"
      "    $setup(data, posedge clock &&& enable, tSU, notifier);\n"
      "    $hold(posedge clock, data &&& enable, tHD, notifier);\n"
      "    $period(posedge clock, tPW, notifier);\n"
      "    $width(negedge preset, tWPC, 0, notifier);\n"
      "    $width(negedge clear, tWPC, 0, notifier);\n"
      "    $recovery(posedge preset, posedge clock, tREC, notifier);\n"
      "    $recovery(posedge clear, posedge clock, tREC, notifier);\n"
      "  endspecify\n"
      "endmodule\n"
      "module top;\n"
      "  reg clock = 0, data = 0, preset = 1, clear = 1;\n"
      "  wire q, qbar;\n"
      "  dff u(q, qbar, clock, data, preset, clear);\n"
      "  initial $monitor(\"%0t %b %b %b\", $time, q, qbar, u.notifier);\n"
      "  initial begin\n"
      "    #20 data = 1; #20 clock = 1;\n"
      "    #10 clock = 0;\n"
      "    #12 data = 0; #8 clock = 1;\n"
      "    #20 $finish;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunCapture(kDesign, f),
            "0 x x x\n46 1 x x\n48 1 0 x\n76 1 x 1\n78 x x 1\n"
            "$finish at time 90\n");
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kSetupViolation,
                              LineHolding(kDesign, "$setup(data, posedge"),
                              "31.3.1"));
}

}  // namespace
