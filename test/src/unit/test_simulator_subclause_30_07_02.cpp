#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "driver/cli_options.h"
#include "elaborator/elaborator.h"
#include "fixture_simulator.h"
#include "fixture_specify_manager.h"
#include "fixture_specify_path_decl.h"
#include "helpers_command_line.h"
#include "lexer/lexer.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/parser.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

PathDelay BuildDelayFromSource(const std::string& specify_body, SimFixture& f) {
  auto c = ElaboratePathDecl("input a, output y", specify_body, f);
  EXPECT_NE(c.decl, nullptr);
  EXPECT_NE(c.design, nullptr);
  LowerAndRun(c.design, f);
  PathDelay pd = BuildPathDelayFromDecl(*c.decl, f.ctx, f.arena);
  InitDefaultPulseLimits(pd);
  return pd;
}

TEST(GlobalPulseLimitScaling, HundredPercentEqualsInertialDefault) {
  SimFixture f;
  PathDelay pd = BuildDelayFromSource("    (a => y) = (7, 9);", f);
  ASSERT_EQ(pd.delays[0], 7u);
  ASSERT_EQ(pd.delays[1], 9u);
  ApplyGlobalPulseLimits(pd, 100, 100);
  EXPECT_EQ(pd.reject_limit[0], 7u);
  EXPECT_EQ(pd.error_limit[0], 7u);
  EXPECT_EQ(pd.reject_limit[1], 9u);
  EXPECT_EQ(pd.error_limit[1], 9u);
}

TEST(GlobalPulseLimitScaling, PercentagesScaleParsedDelay) {
  SimFixture f;
  PathDelay pd = BuildDelayFromSource("    (a => y) = 40;", f);
  ASSERT_EQ(pd.delays[0], 40u);
  ApplyGlobalPulseLimits(pd, 25, 75);
  EXPECT_EQ(pd.reject_limit[0], 10u);
  EXPECT_EQ(pd.error_limit[0], 30u);
}

TEST(GlobalPulseLimitScaling, SpecparamDelayScaledByPercentages) {
  SimFixture f;
  PathDelay pd =
      BuildDelayFromSource("    specparam d = 80;\n    (a => y) = d;", f);
  ASSERT_EQ(pd.delays[0], 80u);
  ApplyGlobalPulseLimits(pd, 50, 100);
  EXPECT_EQ(pd.reject_limit[0], 40u);
  EXPECT_EQ(pd.error_limit[0], 80u);
}

TEST(GlobalPulseLimitScaling, ZeroPercentProducesZeroLimits) {
  SimFixture f;
  PathDelay pd = BuildDelayFromSource("    (a => y) = 40;", f);
  ApplyGlobalPulseLimits(pd, 0, 0);
  EXPECT_EQ(pd.reject_limit[0], 0u);
  EXPECT_EQ(pd.error_limit[0], 0u);
}

TEST(GlobalPulseLimitScaling, ErrorBelowRejectIsClampedUp) {
  SimFixture f;
  PathDelay pd = BuildDelayFromSource("    (a => y) = 100;", f);
  ApplyGlobalPulseLimits(pd, 60, 30);
  EXPECT_EQ(pd.reject_limit[0], 60u);
  EXPECT_EQ(pd.error_limit[0], 60u);
}

TEST(GlobalPulseLimitScaling, PerSlotScalingFromSixDelays) {
  SimFixture f;
  PathDelay pd =
      BuildDelayFromSource("    (a => y) = (10, 20, 30, 40, 50, 60);", f);
  ApplyGlobalPulseLimits(pd, 50, 100);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], pd.delays[i] / 2) << "reject slot " << i;
    EXPECT_EQ(pd.error_limit[i], pd.delays[i]) << "error slot " << i;
  }
}

TEST(GlobalPulseLimitScaling, MinTypMaxDelayScaledByPercentages) {
  SimFixture f;
  PathDelay pd = BuildDelayFromSource("    (a => y) = 6:8:10;", f);
  ASSERT_EQ(pd.delays[0], 8u);
  ApplyGlobalPulseLimits(pd, 50, 100);
  EXPECT_EQ(pd.reject_limit[0], 4u);
  EXPECT_EQ(pd.error_limit[0], 8u);
}

TEST(GlobalPulseLimitScaling, TwelveValueDelayScaledPerSlot) {
  SimFixture f;
  PathDelay pd = BuildDelayFromSource(
      "    (a => y) = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);", f);
  ApplyGlobalPulseLimits(pd, 100, 100);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], pd.delays[i]) << "reject slot " << i;
    EXPECT_EQ(pd.error_limit[i], pd.delays[i]) << "error slot " << i;
  }
}

TEST(GlobalPulseLimitScaling, PropagationDelaysPreserved) {
  SimFixture f;
  PathDelay pd = BuildDelayFromSource("    (a => y) = 40;", f);
  ApplyGlobalPulseLimits(pd, 50, 70);
  for (int i = 0; i < 12; ++i) EXPECT_EQ(pd.delays[i], 40u);
}

TEST(GlobalPulseLimitScaling, PathpulseOverridesGlobalLimits) {
  SimFixture f;
  PathDelay pd = BuildDelayFromSource("    (a => y) = 100;", f);
  ApplyGlobalPulseLimits(pd, 50, 80);
  ApplyPulseControlOverride(pd, 5, true, 9);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 5u);
    EXPECT_EQ(pd.error_limit[i], 9u);
  }
}

TEST(GlobalPulseLimitScaling, PathpulseFromSourceOverridesGlobalScaling) {
  SimFixture f;
  std::string code =
      "module t(input clk, output q);\n"
      "  specify\n"
      "    (clk => q) = 100;\n"
      "    specparam PATHPULSE$clk$q = (5, 9);\n"
      "  endspecify\n"
      "endmodule\n";
  auto fid = f.mgr.AddFile("<test>", code);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  LowerAndRun(design, f);

  SpecifyManager mgr;
  for (auto* item : cu->modules.back()->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      if (si->kind == SpecifyItemKind::kPathDecl) {
        PathDelay pd = BuildPathDelayFromDecl(si->path, f.ctx, f.arena);
        InitDefaultPulseLimits(pd);
        ApplyGlobalPulseLimits(pd, 50, 80);
        mgr.AddPathDelay(pd);
      }
    }
  }
  RegisterPathPulseSpecparams(*cu->modules.back(), f, mgr);

  const PathDelay* p = nullptr;
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.src_port == "clk" && pd.dst_port == "q") p = &pd;
  }
  ASSERT_NE(p, nullptr);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(p->reject_limit[i], 5u);
    EXPECT_EQ(p->error_limit[i], 9u);
  }
}

TEST(GlobalPulseLimitScaling, DefaultGlobalPercentagesAreHundred) {
  SpecifyManager mgr;
  EXPECT_EQ(mgr.RejectPulseLimitPercent(), 100u);
  EXPECT_EQ(mgr.ErrorPulseLimitPercent(), 100u);
}

TEST(GlobalPulseLimitScaling, InvocationOptionsSetThePercentages) {
  CliOptions opts;
  ASSERT_TRUE(ParseCommandLine(
      {"--pulse-reject-limit", "40", "--pulse-error-limit", "80"}, opts));
  SpecifyManager mgr;
  ApplyPulseControlOptions(opts, mgr);
  EXPECT_EQ(mgr.RejectPulseLimitPercent(), 40u);
  EXPECT_EQ(mgr.ErrorPulseLimitPercent(), 80u);
}

TEST(GlobalPulseLimitScaling, PercentageAboveHundredIsRefused) {
  CliOptions opts;
  std::string err;
  EXPECT_FALSE(ParseCommandLineCapturingStderr({"--pulse-error-limit", "101"},
                                               opts, err));
  EXPECT_TRUE(opts.rejected_argument);
  EXPECT_NE(err.find("--pulse-error-limit expects a percentage from 0 to 100: "
                     "101"),
            std::string::npos)
      << err;
}

TEST(GlobalPulseLimitScaling, ErrorPercentageBelowRejectIsReportedAndRaised) {
  CliOptions opts;
  std::string err;
  EXPECT_TRUE(ParseCommandLineCapturingStderr(
      {"--pulse-reject-limit", "60", "--pulse-error-limit", "20"}, opts, err));
  EXPECT_EQ(opts.pulse_reject_percent, 60u);
  EXPECT_EQ(opts.pulse_error_percent, 60u);
  EXPECT_NE(err.find("--pulse-error-limit 20 is smaller than "
                     "--pulse-reject-limit 60"),
            std::string::npos)
      << err;
}

TEST(GlobalPulseLimitScaling, RejectPercentageAboveHundredIsRefused) {
  CliOptions opts;
  std::string err;
  EXPECT_FALSE(ParseCommandLineCapturingStderr({"--pulse-reject-limit", "101"},
                                               opts, err));
  EXPECT_TRUE(opts.rejected_argument);
  EXPECT_NE(
      err.find("--pulse-reject-limit expects a percentage from 0 to 100: 101"),
      std::string::npos)
      << err;
}

TEST(GlobalPulseLimitScaling, NegativePercentageIsRefused) {
  for (const char* option : {"--pulse-reject-limit", "--pulse-error-limit"}) {
    CliOptions opts;
    std::string err;
    EXPECT_FALSE(ParseCommandLineCapturingStderr({option, "-5"}, opts, err))
        << option;
    EXPECT_TRUE(opts.rejected_argument) << option;
    EXPECT_NE(err.find(std::string(option) +
                       " expects a number that is not negative: -5"),
              std::string::npos)
        << err;
  }
}

TEST(GlobalPulseLimitScaling, NonIntegerPercentageIsRefused) {
  for (const char* option : {"--pulse-reject-limit", "--pulse-error-limit"}) {
    for (const char* value : {"50.5", "half"}) {
      CliOptions opts;
      std::string err;
      EXPECT_FALSE(ParseCommandLineCapturingStderr({option, value}, opts, err))
          << option << " " << value;
      EXPECT_TRUE(opts.rejected_argument) << option << " " << value;
      EXPECT_NE(err.find(std::string(option) + " expects a number: " + value),
                std::string::npos)
          << err;
    }
  }
}

TEST(GlobalPulseLimitScaling, DISABLED_RefusedErrorPercentageDrawsOneReport) {
  CliOptions opts;
  std::string err;
  EXPECT_FALSE(ParseCommandLineCapturingStderr({"--pulse-error-limit", "50.5"},
                                               opts, err));
  EXPECT_EQ(err.find("is smaller than"), std::string::npos) << err;
}

TEST(GlobalPulseLimitScaling, BoundaryPercentagesAreAccepted) {
  const std::vector<std::vector<std::string>> kArgLists = {
      {"--pulse-reject-limit", "0", "--pulse-error-limit", "0"},
      {"--pulse-reject-limit", "0", "--pulse-error-limit", "100"},
      {"--pulse-reject-limit", "100", "--pulse-error-limit", "100"},
  };
  for (const auto& args : kArgLists) {
    CliOptions opts;
    std::string err;
    EXPECT_TRUE(ParseCommandLineCapturingStderr(args, opts, err)) << args[1];
    EXPECT_FALSE(opts.rejected_argument) << args[1] << " " << args[3];
    EXPECT_EQ(err, "") << args[1] << " " << args[3];
    SpecifyManager mgr;
    ApplyPulseControlOptions(opts, mgr);
    EXPECT_EQ(mgr.RejectPulseLimitPercent(), std::stoul(args[1]));
    EXPECT_EQ(mgr.ErrorPulseLimitPercent(), std::stoul(args[3]));
  }
}

TEST(GlobalPulseLimitScaling, WithoutEitherOptionBothPercentagesAreHundred) {
  CliOptions opts;
  ASSERT_TRUE(ParseCommandLine({}, opts));
  SpecifyManager mgr;
  ApplyPulseControlOptions(opts, mgr);
  EXPECT_EQ(mgr.RejectPulseLimitPercent(), 100u);
  EXPECT_EQ(mgr.ErrorPulseLimitPercent(), 100u);
}

TEST(GlobalPulseLimitScaling, RejectOptionAloneLeavesErrorAtHundred) {
  CliOptions opts;
  std::string err;
  EXPECT_TRUE(ParseCommandLineCapturingStderr({"--pulse-reject-limit", "40"},
                                              opts, err));
  EXPECT_EQ(err, "");
  EXPECT_EQ(opts.pulse_reject_percent, 40u);
  EXPECT_EQ(opts.pulse_error_percent, 100u);
}

TEST(GlobalPulseLimitScaling, ErrorOptionAloneBelowDefaultRejectIsRaised) {
  CliOptions opts;
  std::string err;
  EXPECT_TRUE(ParseCommandLineCapturingStderr({"--pulse-error-limit", "80"},
                                              opts, err));
  EXPECT_EQ(opts.pulse_reject_percent, 100u);
  EXPECT_EQ(opts.pulse_error_percent, 100u);
  EXPECT_NE(err.find("--pulse-error-limit 80 is smaller than "
                     "--pulse-reject-limit 100"),
            std::string::npos)
      << err;
}

TEST(GlobalPulseLimitScaling, EqualPercentagesAreAcceptedWithoutReport) {
  CliOptions opts;
  std::string err;
  EXPECT_TRUE(ParseCommandLineCapturingStderr(
      {"--pulse-reject-limit", "60", "--pulse-error-limit", "60"}, opts, err));
  EXPECT_EQ(err, "");
  EXPECT_EQ(opts.pulse_reject_percent, 60u);
  EXPECT_EQ(opts.pulse_error_percent, 60u);
}

std::string RunPulseThroughCell(const std::vector<std::string>& args,
                                const std::string& specify_body) {
  SimFixture f;
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine(args, opts));
  ApplyPulseControlOptions(opts, f.ctx.AcquireSpecifyManager());
  return RunCapture(
      "module drive(input a, output y);\n"
      "  assign y = a;\n"
      "  specify\n" +
          specify_body +
          "  endspecify\n"
          "endmodule\n"
          "module top;\n"
          "  logic in;\n"
          "  wire out;\n"
          "  drive c(.a(in), .y(out));\n"
          "  always @(out) if ($time > 0) $display(\"t=%0t y=%b\", $time, "
          "out);\n"
          "  initial begin\n"
          "    in = 1;\n"
          "    #10 in = 0;\n"
          "    #4 in = 1;\n"
          "  end\n"
          "endmodule\n",
      f);
}

TEST(GlobalPulseLimitRun, WithoutOptionsANarrowPulseIsRejected) {
  EXPECT_EQ(RunPulseThroughCell({}, "    (a => y) = 7;\n"), "t=7 y=1\n");
}

TEST(GlobalPulseLimitRun, HalvedLimitsLetTheSamePulsePropagate) {
  EXPECT_EQ(RunPulseThroughCell(
                {"--pulse-reject-limit", "50", "--pulse-error-limit", "50"},
                "    (a => y) = 7;\n"),
            "t=7 y=1\nt=17 y=0\nt=21 y=1\n");
}

TEST(GlobalPulseLimitRun, PulseBetweenTheScaledLimitsIsFilteredToX) {
  EXPECT_EQ(RunPulseThroughCell(
                {"--pulse-reject-limit", "20", "--pulse-error-limit", "100"},
                "    (a => y) = 7;\n"),
            "t=7 y=1\nt=17 y=x\nt=21 y=1\n");
}

TEST(GlobalPulseLimitRun, PathpulseTakesPrecedenceOverTheOptions) {
  EXPECT_EQ(RunPulseThroughCell(
                {"--pulse-reject-limit", "50", "--pulse-error-limit", "50"},
                "    (a => y) = 7;\n"
                "    specparam PATHPULSE$ = (5);\n"),
            "t=7 y=1\n");
}

TEST(GlobalPulseLimitRun, PathSpecificPathpulseTakesPrecedenceOverTheOptions) {
  EXPECT_EQ(RunPulseThroughCell(
                {"--pulse-reject-limit", "50", "--pulse-error-limit", "50"},
                "    (a => y) = 7;\n"
                "    specparam PATHPULSE$a$y = (5);\n"),
            "t=7 y=1\n");
}

TEST(GlobalPulseLimitScaling, DeclaredPathTakesTheGlobalPercentages) {
  SimFixture f;
  f.ctx.AcquireSpecifyManager().SetGlobalPulseLimitPercents(50, 80);
  auto c =
      ElaboratePathDecl("input a, output y", "    (a => y) = (10, 20);", f);
  ASSERT_NE(c.design, nullptr);
  LowerAndRun(c.design, f);
  const auto& paths = f.ctx.AcquireSpecifyManager().GetPathDelays();
  ASSERT_EQ(paths.size(), 1u);
  EXPECT_EQ(paths[0].reject_limit[0], 5u);
  EXPECT_EQ(paths[0].error_limit[0], 8u);
  EXPECT_EQ(paths[0].reject_limit[1], 10u);
  EXPECT_EQ(paths[0].error_limit[1], 16u);
}

}  // namespace
