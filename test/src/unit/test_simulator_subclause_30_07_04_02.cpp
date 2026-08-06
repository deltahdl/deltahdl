#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "fixture_specify_manager.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// §30.7.4.2 governs negative pulse detection: when a module path's unequal
// delays schedule the trailing edge before the leading edge, the leading edge
// is cancelled (noshowcancelled, the default) or made visible as x
// (showcancelled). The showcancelled mode is produced by the showcancelled/
// noshowcancelled declarations of Syntax 30-9, so every test drives that real
// specify source through the full parse/elaborate/lower/run pipeline and then
// registers each declaration's mode onto the production SpecifyManager. The
// runtime rule is observed through SpecifyManager::ResolveShowCancelled and the
// ScheduleNegativePulse/IsNegativePulse functions rather than by hand-building
// a mode value. The specify runtime is not wired into RTLIR, so the
// registration step mirrors how §30.7.4.1's tests feed parsed pulse styles into
// the manager.
void LoadShowCancelledFromSource(const std::string& specify_body, SimFixture& f,
                                 SpecifyManager& mgr) {
  auto* cu = RunSpecifyBlockSource(specify_body, f);
  ASSERT_NE(cu, nullptr);
  RegisterShowCancelled(*cu->modules.back(), mgr);
}

// A noshowcancelled declaration selects the default behavior: a negative pulse
// cancels the leading edge with no x indication.
TEST(NegativePulseDetectionSim, NoshowcancelledCancelsLeadingEdge) {
  SimFixture f;
  SpecifyManager mgr;
  LoadShowCancelledFromSource("    noshowcancelled out;", f, mgr);
  EXPECT_EQ(mgr.ResolveShowCancelled("out"), ShowCancelled::kNoshowcancelled);
  NegativePulseSchedule s = ScheduleNegativePulse(
      mgr.ResolveShowCancelled("out"), PulseStyle::kOnEvent,
      /*detect_time=*/15, /*scheduled_leading_time=*/16);
  EXPECT_FALSE(s.force_x);
}

// noshowcancelled is the default: an output that no showcancelled declaration
// names resolves to noshowcancelled even when another output in the same block
// was declared showcancelled.
TEST(NegativePulseDetectionSim, DefaultIsNoshowcancelledForUndeclaredOutput) {
  SimFixture f;
  SpecifyManager mgr;
  LoadShowCancelledFromSource("    showcancelled out;", f, mgr);
  EXPECT_EQ(mgr.ResolveShowCancelled("other"), ShowCancelled::kNoshowcancelled);
}

// list_of_path_outputs form: one showcancelled declaration listing several
// outputs selects the mode for every output it names.
TEST(NegativePulseDetectionSim, MultipleOutputsShareShowcancelled) {
  SimFixture f;
  SpecifyManager mgr;
  LoadShowCancelledFromSource("    showcancelled a, b, c;", f, mgr);
  EXPECT_EQ(mgr.ResolveShowCancelled("a"), ShowCancelled::kShowcancelled);
  EXPECT_EQ(mgr.ResolveShowCancelled("b"), ShowCancelled::kShowcancelled);
  EXPECT_EQ(mgr.ResolveShowCancelled("c"), ShowCancelled::kShowcancelled);
}

// The showcancelled invocation option takes precedence over a specify block
// declaration: an output declared showcancelled in source resolves to the
// globally selected noshowcancelled once the invocation option is present.
TEST(NegativePulseDetectionSim, InvocationOptionOverridesSpecifyBlock) {
  SimFixture f;
  SpecifyManager mgr;
  LoadShowCancelledFromSource("    showcancelled out;", f, mgr);
  ASSERT_EQ(mgr.ResolveShowCancelled("out"), ShowCancelled::kShowcancelled);
  mgr.SetGlobalShowCancelled(ShowCancelled::kNoshowcancelled);
  EXPECT_EQ(mgr.ResolveShowCancelled("out"), ShowCancelled::kNoshowcancelled);
  NegativePulseSchedule s = ScheduleNegativePulse(
      mgr.ResolveShowCancelled("out"), PulseStyle::kOnEvent,
      /*detect_time=*/15, /*scheduled_leading_time=*/16);
  EXPECT_FALSE(s.force_x);
}

// The default mode is a property of a fresh manager, independent of any source:
// any output resolves to noshowcancelled when nothing has been declared or
// selected globally.
TEST(NegativePulseDetectionSim, DefaultManagerResolvesNoshowcancelled) {
  SpecifyManager mgr;
  EXPECT_EQ(mgr.ResolveShowCancelled("anything"),
            ShowCancelled::kNoshowcancelled);
}

// The showcancelled invocation option also wins in the other direction: an
// output declared noshowcancelled in source resolves to the globally selected
// showcancelled once the invocation option is present, so its negative pulse is
// forced to x despite the block declaration. Complements the opposite-polarity
// override test above.
TEST(NegativePulseDetectionSim,
     GlobalShowcancelledOverridesBlockNoshowcancelled) {
  SimFixture f;
  SpecifyManager mgr;
  LoadShowCancelledFromSource("    noshowcancelled out;", f, mgr);
  ASSERT_EQ(mgr.ResolveShowCancelled("out"), ShowCancelled::kNoshowcancelled);
  mgr.SetGlobalShowCancelled(ShowCancelled::kShowcancelled);
  EXPECT_EQ(mgr.ResolveShowCancelled("out"), ShowCancelled::kShowcancelled);
  NegativePulseSchedule s = ScheduleNegativePulse(
      mgr.ResolveShowCancelled("out"), PulseStyle::kOnEvent,
      /*detect_time=*/15, /*scheduled_leading_time=*/16);
  EXPECT_TRUE(s.force_x);
  EXPECT_EQ(s.x_time, 16u);
}

// End-to-end through the §30.7.4.1 dependency: §30.7.4.2 says the pulse-
// filtering style decides WHEN a shown-cancelled negative pulse transitions to
// x — on-event keeps the already-scheduled leading time, on-detect advances it
// to detection. That style is itself produced by §30.7.4.1's
// pulsestyle_ondetect / pulsestyle_onevent declarations, so this test builds it
// from that real source instead of passing a hand-picked enum. One specify
// block declares two outputs showcancelled; o1 additionally takes
// pulsestyle_ondetect while o2 keeps the default on-event. Both the
// showcancelled mode and the pulse style are resolved from the parsed AST
// through the production SpecifyManager, and only then does
// ScheduleNegativePulse use the resolved style to place the to-x transition.
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

  // Both outputs are shown-cancelled; only the pulse style differs by source.
  ASSERT_EQ(mgr.ResolveShowCancelled("o1"), ShowCancelled::kShowcancelled);
  ASSERT_EQ(mgr.ResolveShowCancelled("o2"), ShowCancelled::kShowcancelled);
  ASSERT_EQ(mgr.ResolvePulseStyle("o1"), PulseStyle::kOnDetect);
  ASSERT_EQ(mgr.ResolvePulseStyle("o2"), PulseStyle::kOnEvent);  // default

  // o1 (on-detect from source) advances the to-x transition to detection; o2
  // (default on-event) keeps the scheduled leading-edge time. Both force x.
  NegativePulseSchedule s1 = ScheduleNegativePulse(
      mgr.ResolveShowCancelled("o1"), mgr.ResolvePulseStyle("o1"),
      /*detect_time=*/15, /*scheduled_leading_time=*/16);
  EXPECT_TRUE(s1.force_x);
  EXPECT_EQ(s1.x_time, 15u);

  NegativePulseSchedule s2 = ScheduleNegativePulse(
      mgr.ResolveShowCancelled("o2"), mgr.ResolvePulseStyle("o2"),
      /*detect_time=*/15, /*scheduled_leading_time=*/16);
  EXPECT_TRUE(s2.force_x);
  EXPECT_EQ(s2.x_time, 16u);
}

// End-to-end through the §30.5.1 dependency: a negative pulse is a property of
// the module path's unequal delays, so this test produces those delays from the
// real (in => out) = (4, 6) source of Figure 30-7. One specify block carries a
// showcancelled declaration and the module path delay for the same output (the
// showcancelled precedes the path, so it is legal per §30.7.4.2). The rise/fall
// delays are built by §30.5.1's BuildPathDelayFromDecl; an input pulse whose
// leading edge takes the longer delay and trailing edge the shorter one leaves
// the trailing output scheduled before the leading output, which
// IsNegativePulse confirms, and only then does showcancelled force the pulse
// to x — contrasted against the silent cancel a default output would take.
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
  ASSERT_EQ(pd.delays[0], 4u);  // rise delay from the real source
  ASSERT_EQ(pd.delays[1], 6u);  // fall delay from the real source

  // An input pulse at time 10 (leading, taking the fall delay to the output)
  // and 11 (trailing, taking the rise delay) schedules the leading output at
  // 10 + 6 = 16 and the trailing output at 11 + 4 = 15 — a negative pulse.
  const uint64_t kLeading = 10 + pd.delays[1];   // 16
  const uint64_t kTrailing = 11 + pd.delays[0];  // 15
  ASSERT_TRUE(IsNegativePulse(kLeading, kTrailing));

  // §30.7.4.2: the showcancelled declaration forces the negative pulse to x.
  ASSERT_EQ(mgr.ResolveShowCancelled("out"), ShowCancelled::kShowcancelled);
  NegativePulseSchedule shown = ScheduleNegativePulse(
      mgr.ResolveShowCancelled("out"), PulseStyle::kOnEvent,
      /*detect_time=*/kTrailing, /*scheduled_leading_time=*/kLeading);
  EXPECT_TRUE(shown.force_x);
  EXPECT_EQ(shown.x_time, kLeading);

  // A default (noshowcancelled) output on the same negative pulse cancels the
  // leading edge silently.
  NegativePulseSchedule hidden = ScheduleNegativePulse(
      mgr.ResolveShowCancelled("undeclared"), PulseStyle::kOnEvent,
      /*detect_time=*/kTrailing, /*scheduled_leading_time=*/kLeading);
  EXPECT_FALSE(hidden.force_x);
}

}  // namespace
