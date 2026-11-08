#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "driver/cli_options.h"
#include "fixture_simulator.h"
#include "fixture_specify_manager.h"
#include "helpers_command_line.h"
#include "parser/ast_specify.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

void LoadPulseStylesFromSource(const std::string& specify_body, SimFixture& f,
                               SpecifyManager& mgr) {
  auto* cu = RunSpecifyBlockSource(specify_body, f);
  ASSERT_NE(cu, nullptr);
  RegisterPulseStyles(*cu->modules.back(), mgr);
}

TEST(PulseFilterStyleSim, OneventKeepsScheduledLeadingEdge) {
  SimFixture f;
  SpecifyManager mgr;
  LoadPulseStylesFromSource("    pulsestyle_onevent out;", f, mgr);
  EXPECT_EQ(mgr.ResolvePulseStyle("out"), PulseStyle::kOnEvent);
  EXPECT_EQ(FilteredPulseLeadingXTime(mgr.ResolvePulseStyle("out"), 10, 14),
            14u);
}

TEST(PulseFilterStyleSim, OndetectAdvancesLeadingEdgeToDetection) {
  SimFixture f;
  SpecifyManager mgr;
  LoadPulseStylesFromSource("    pulsestyle_ondetect out;", f, mgr);
  EXPECT_EQ(mgr.ResolvePulseStyle("out"), PulseStyle::kOnDetect);
  EXPECT_EQ(FilteredPulseLeadingXTime(mgr.ResolvePulseStyle("out"), 10, 14),
            10u);
}

TEST(PulseFilterStyleSim, DefaultStyleIsOnEventForUndeclaredOutput) {
  SimFixture f;
  SpecifyManager mgr;
  LoadPulseStylesFromSource("    pulsestyle_ondetect out;", f, mgr);
  EXPECT_EQ(mgr.ResolvePulseStyle("other"), PulseStyle::kOnEvent);
  EXPECT_EQ(FilteredPulseLeadingXTime(mgr.ResolvePulseStyle("other"), 10, 14),
            14u);
}

TEST(PulseFilterStyleSim, MultipleOutputsShareDeclaredStyle) {
  SimFixture f;
  SpecifyManager mgr;
  LoadPulseStylesFromSource("    pulsestyle_ondetect a, b, c;", f, mgr);
  EXPECT_EQ(mgr.ResolvePulseStyle("a"), PulseStyle::kOnDetect);
  EXPECT_EQ(mgr.ResolvePulseStyle("b"), PulseStyle::kOnDetect);
  EXPECT_EQ(mgr.ResolvePulseStyle("c"), PulseStyle::kOnDetect);
}

TEST(PulseFilterStyleSim, InvocationOptionOverridesSpecifyBlock) {
  SimFixture f;
  SpecifyManager mgr;
  LoadPulseStylesFromSource("    pulsestyle_ondetect out;", f, mgr);
  ASSERT_EQ(mgr.ResolvePulseStyle("out"), PulseStyle::kOnDetect);
  mgr.SetGlobalPulseStyle(PulseStyle::kOnEvent);
  EXPECT_EQ(mgr.ResolvePulseStyle("out"), PulseStyle::kOnEvent);
  EXPECT_EQ(FilteredPulseLeadingXTime(mgr.ResolvePulseStyle("out"), 10, 14),
            14u);
}

TEST(PulseFilterStyleSim, DefaultManagerResolvesOnEvent) {
  SpecifyManager mgr;
  EXPECT_EQ(mgr.ResolvePulseStyle("anything"), PulseStyle::kOnEvent);
}

TEST(PulseFilterStyleSim, OndetectGovernsPulseClassifiedToXFromSource) {
  SimFixture f;
  std::string code =
      "module t(input a, output y);\n"
      "  specify\n"
      "    pulsestyle_ondetect y;\n"
      "    (a => y) = (7, 9);\n"
      "  endspecify\n"
      "endmodule\n";
  auto* cu = RunModuleSource(code, f);
  ASSERT_NE(cu, nullptr);

  SpecifyManager mgr;
  RegisterPulseStyles(*cu->modules.back(), mgr);
  const SpecifyPathDecl* path = FirstPathDeclIn(*cu->modules.back());
  ASSERT_NE(path, nullptr);

  PathDelay pd = BuildPathDelayFromDecl(*path, f.ctx, f.arena);
  InitDefaultPulseLimits(pd);
  ASSERT_EQ(pd.delays[0], 7u);

  ApplyGlobalPulseLimits(pd, 30, 100);
  ASSERT_EQ(pd.reject_limit[0], 2u);
  ASSERT_EQ(pd.error_limit[0], 7u);

  ASSERT_EQ(ClassifyPulse(4, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kForceX);

  ASSERT_EQ(mgr.ResolvePulseStyle("y"), PulseStyle::kOnDetect);
  const uint64_t kDetect = 10;
  const uint64_t kScheduled = 14;
  EXPECT_EQ(FilteredPulseLeadingXTime(mgr.ResolvePulseStyle("y"), kDetect,
                                      kScheduled),
            kDetect);
  EXPECT_EQ(
      FilteredPulseLeadingXTime(PulseStyle::kOnEvent, kDetect, kScheduled),
      kScheduled);
}

TEST(PulseStyleRun, OnDetectDrivesAFilteredPulseXFromItsDetection) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module mybuf(input a, output y);\n"
                       "  assign y = a;\n"
                       "  specify\n"
                       "    pulsestyle_ondetect y;\n"
                       "    specparam PATHPULSE$ = (1, 5);\n"
                       "    (a => y) = (7, 9);\n"
                       "  endspecify\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic a;\n"
                       "  wire ty;\n"
                       "  mybuf u(.a(a), .y(ty));\n"
                       "  always @(ty) if ($time > 0)\n"
                       "    $display(\"t=%0t y=%b\", $time, ty);\n"
                       "  initial begin\n"
                       "    a = 1;\n"
                       "    #10 a = 0;\n"
                       "    #4 a = 1;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t=7 y=1\nt=14 y=x\nt=21 y=1\n");
}

TEST(PulseFilterStyleSim, OnDetectInvocationOptionOverridesTheDeclaration) {
  SimFixture f;
  SpecifyManager mgr;
  LoadPulseStylesFromSource("    pulsestyle_onevent out;", f, mgr);
  CliOptions opts;
  ASSERT_TRUE(ParseCommandLine({"--pulse-style-ondetect"}, opts));
  ApplyPulseControlOptions(opts, mgr);
  EXPECT_EQ(mgr.ResolvePulseStyle("out"), PulseStyle::kOnDetect);
}

TEST(PulseFilterStyleSim, OnEventInvocationOptionOverridesTheDeclaration) {
  SimFixture f;
  SpecifyManager mgr;
  LoadPulseStylesFromSource("    pulsestyle_ondetect out;", f, mgr);
  CliOptions opts;
  ASSERT_TRUE(ParseCommandLine({"--pulse-style-onevent"}, opts));
  ApplyPulseControlOptions(opts, mgr);
  EXPECT_EQ(mgr.ResolvePulseStyle("out"), PulseStyle::kOnEvent);
}

TEST(PulseFilterStyleSim, WithoutAStyleOptionTheDeclarationStands) {
  SimFixture f;
  SpecifyManager mgr;
  LoadPulseStylesFromSource("    pulsestyle_ondetect out;", f, mgr);
  CliOptions opts;
  ASSERT_TRUE(ParseCommandLine({}, opts));
  ApplyPulseControlOptions(opts, mgr);
  EXPECT_EQ(mgr.ResolvePulseStyle("out"), PulseStyle::kOnDetect);
}

}  // namespace
