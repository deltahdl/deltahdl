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

void LoadShowCancelledFromSource(const std::string& specify_body, SimFixture& f,
                                 SpecifyManager& mgr) {
  auto* cu = RunSpecifyBlockSource(specify_body, f);
  ASSERT_NE(cu, nullptr);
  RegisterShowCancelled(*cu->modules.back(), mgr);
}

TEST(NegativePulseDetectionSim, NoshowcancelledCancelsLeadingEdge) {
  SimFixture f;
  SpecifyManager mgr;
  LoadShowCancelledFromSource("    noshowcancelled out;", f, mgr);
  EXPECT_EQ(mgr.ResolveShowCancelled("out"), ShowCancelled::kNoshowcancelled);
  NegativePulseSchedule s = ScheduleNegativePulse(
      mgr.ResolveShowCancelled("out"), PulseStyle::kOnEvent, 15, 16);
  EXPECT_FALSE(s.force_x);
}

TEST(NegativePulseDetectionSim, DefaultIsNoshowcancelledForUndeclaredOutput) {
  SimFixture f;
  SpecifyManager mgr;
  LoadShowCancelledFromSource("    showcancelled out;", f, mgr);
  EXPECT_EQ(mgr.ResolveShowCancelled("other"), ShowCancelled::kNoshowcancelled);
}

TEST(NegativePulseDetectionSim, MultipleOutputsShareShowcancelled) {
  SimFixture f;
  SpecifyManager mgr;
  LoadShowCancelledFromSource("    showcancelled a, b, c;", f, mgr);
  EXPECT_EQ(mgr.ResolveShowCancelled("a"), ShowCancelled::kShowcancelled);
  EXPECT_EQ(mgr.ResolveShowCancelled("b"), ShowCancelled::kShowcancelled);
  EXPECT_EQ(mgr.ResolveShowCancelled("c"), ShowCancelled::kShowcancelled);
}

TEST(NegativePulseDetectionSim, InvocationOptionOverridesSpecifyBlock) {
  SimFixture f;
  SpecifyManager mgr;
  LoadShowCancelledFromSource("    showcancelled out;", f, mgr);
  ASSERT_EQ(mgr.ResolveShowCancelled("out"), ShowCancelled::kShowcancelled);
  mgr.SetGlobalShowCancelled(ShowCancelled::kNoshowcancelled);
  EXPECT_EQ(mgr.ResolveShowCancelled("out"), ShowCancelled::kNoshowcancelled);
  NegativePulseSchedule s = ScheduleNegativePulse(
      mgr.ResolveShowCancelled("out"), PulseStyle::kOnEvent, 15, 16);
  EXPECT_FALSE(s.force_x);
}

TEST(NegativePulseDetectionSim, DefaultManagerResolvesNoshowcancelled) {
  SpecifyManager mgr;
  EXPECT_EQ(mgr.ResolveShowCancelled("anything"),
            ShowCancelled::kNoshowcancelled);
}

TEST(NegativePulseDetectionSim,
     GlobalShowcancelledOverridesBlockNoshowcancelled) {
  SimFixture f;
  SpecifyManager mgr;
  LoadShowCancelledFromSource("    noshowcancelled out;", f, mgr);
  ASSERT_EQ(mgr.ResolveShowCancelled("out"), ShowCancelled::kNoshowcancelled);
  mgr.SetGlobalShowCancelled(ShowCancelled::kShowcancelled);
  EXPECT_EQ(mgr.ResolveShowCancelled("out"), ShowCancelled::kShowcancelled);
  NegativePulseSchedule s = ScheduleNegativePulse(
      mgr.ResolveShowCancelled("out"), PulseStyle::kOnEvent, 15, 16);
  EXPECT_TRUE(s.force_x);
  EXPECT_EQ(s.x_time, 16u);
}

TEST(NegativePulseDetectionSim,
     ResolvedPulseStyleFromSourceTimesNegativePulseX) {
  SimFixture f;
  std::string code =
      "module t;\n"
      "  specify\n"
      "    showcancelled o1, o2;\n"
      "    pulsestyle_ondetect o1;\n"
      "  endspecify\n"
      "endmodule\n";
  auto* cu = RunModuleSource(code, f);
  ASSERT_NE(cu, nullptr);

  SpecifyManager mgr;
  RegisterShowCancelled(*cu->modules.back(), mgr);
  RegisterPulseStyles(*cu->modules.back(), mgr);

  ASSERT_EQ(mgr.ResolveShowCancelled("o1"), ShowCancelled::kShowcancelled);
  ASSERT_EQ(mgr.ResolveShowCancelled("o2"), ShowCancelled::kShowcancelled);
  ASSERT_EQ(mgr.ResolvePulseStyle("o1"), PulseStyle::kOnDetect);
  ASSERT_EQ(mgr.ResolvePulseStyle("o2"), PulseStyle::kOnEvent);

  NegativePulseSchedule s1 = ScheduleNegativePulse(
      mgr.ResolveShowCancelled("o1"), mgr.ResolvePulseStyle("o1"), 15, 16);
  EXPECT_TRUE(s1.force_x);
  EXPECT_EQ(s1.x_time, 15u);

  NegativePulseSchedule s2 = ScheduleNegativePulse(
      mgr.ResolveShowCancelled("o2"), mgr.ResolvePulseStyle("o2"), 15, 16);
  EXPECT_TRUE(s2.force_x);
  EXPECT_EQ(s2.x_time, 16u);
}

TEST(NegativePulseDetectionSim, NegativePulseFromUnequalDelaysForcesX) {
  SimFixture f;
  std::string code =
      "module t(input in, output out);\n"
      "  specify\n"
      "    showcancelled out;\n"
      "    (in => out) = (4, 6);\n"
      "  endspecify\n"
      "endmodule\n";
  auto* cu = RunModuleSource(code, f);
  ASSERT_NE(cu, nullptr);

  SpecifyManager mgr;
  RegisterShowCancelled(*cu->modules.back(), mgr);
  const SpecifyPathDecl* path = FirstPathDeclIn(*cu->modules.back());
  ASSERT_NE(path, nullptr);

  PathDelay pd = BuildPathDelayFromDecl(*path, f.ctx, f.arena);
  ASSERT_EQ(pd.delays[0], 4u);
  ASSERT_EQ(pd.delays[1], 6u);

  const uint64_t kLeading = 10 + pd.delays[1];
  const uint64_t kTrailing = 11 + pd.delays[0];
  ASSERT_TRUE(IsNegativePulse(kLeading, kTrailing));

  ASSERT_EQ(mgr.ResolveShowCancelled("out"), ShowCancelled::kShowcancelled);
  NegativePulseSchedule shown =
      ScheduleNegativePulse(mgr.ResolveShowCancelled("out"),
                            PulseStyle::kOnEvent, kTrailing, kLeading);
  EXPECT_TRUE(shown.force_x);
  EXPECT_EQ(shown.x_time, kLeading);

  NegativePulseSchedule hidden =
      ScheduleNegativePulse(mgr.ResolveShowCancelled("undeclared"),
                            PulseStyle::kOnEvent, kTrailing, kLeading);
  EXPECT_FALSE(hidden.force_x);
}

TEST(NegativePulseDetectionSim, ShowcancelledOptionOverridesTheDeclaration) {
  SimFixture f;
  SpecifyManager mgr;
  LoadShowCancelledFromSource("    noshowcancelled out;", f, mgr);
  CliOptions opts;
  ASSERT_TRUE(ParseCommandLine({"--showcancelled"}, opts));
  ApplyPulseControlOptions(opts, mgr);
  EXPECT_EQ(mgr.ResolveShowCancelled("out"), ShowCancelled::kShowcancelled);
}

TEST(NegativePulseDetectionSim, NoshowcancelledOptionOverridesTheDeclaration) {
  SimFixture f;
  SpecifyManager mgr;
  LoadShowCancelledFromSource("    showcancelled out;", f, mgr);
  CliOptions opts;
  ASSERT_TRUE(ParseCommandLine({"--noshowcancelled"}, opts));
  ApplyPulseControlOptions(opts, mgr);
  EXPECT_EQ(mgr.ResolveShowCancelled("out"), ShowCancelled::kNoshowcancelled);
}

}  // namespace
