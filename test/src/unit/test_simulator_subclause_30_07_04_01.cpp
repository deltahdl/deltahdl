#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "fixture_specify_manager.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// §30.7.4.1 selects the pulse-filtering STYLE (on-event vs on-detect) that
// applies when a pulse is filtered to x. The style is produced by the
// pulsestyle_onevent/pulsestyle_ondetect declarations of Syntax 30-8, so every
// test below drives that real specify source through the full parse/elaborate/
// lower/run pipeline and then registers each declaration's style onto the
// production SpecifyManager. The runtime rule is observed through
// SpecifyManager::ResolvePulseStyle and FilteredPulseLeadingXTime rather than
// by hand-building a style value. The specify runtime is not wired into RTLIR,
// so the registration step mirrors how §30.7.2's tests feed parsed path delays
// into the manager.
void LoadPulseStylesFromSource(const std::string& specify_body, SimFixture& f,
                               SpecifyManager& mgr) {
  auto* cu = RunSpecifyBlockSource(specify_body, f);
  ASSERT_NE(cu, nullptr);
  RegisterPulseStyles(*cu->modules.back(), mgr);
}

// A pulsestyle_onevent declaration selects the on-event style, and under
// on-event the leading edge of an x-filtered pulse keeps its already-scheduled
// transition time.
TEST(PulseFilterStyleSim, OneventKeepsScheduledLeadingEdge) {
  SimFixture f;
  SpecifyManager mgr;
  LoadPulseStylesFromSource("    pulsestyle_onevent out;", f, mgr);
  EXPECT_EQ(mgr.ResolvePulseStyle("out"), PulseStyle::kOnEvent);
  EXPECT_EQ(FilteredPulseLeadingXTime(mgr.ResolvePulseStyle("out"),
                                      /*detect_time=*/10,
                                      /*scheduled_leading_time=*/14),
            14u);
}

// A pulsestyle_ondetect declaration selects the on-detect style, which moves
// the leading x transition to the moment the pulse is detected (earlier than
// the scheduled leading-edge time).
TEST(PulseFilterStyleSim, OndetectAdvancesLeadingEdgeToDetection) {
  SimFixture f;
  SpecifyManager mgr;
  LoadPulseStylesFromSource("    pulsestyle_ondetect out;", f, mgr);
  EXPECT_EQ(mgr.ResolvePulseStyle("out"), PulseStyle::kOnDetect);
  EXPECT_EQ(FilteredPulseLeadingXTime(mgr.ResolvePulseStyle("out"),
                                      /*detect_time=*/10,
                                      /*scheduled_leading_time=*/14),
            10u);
}

// On-event is the default: an output that no pulsestyle declaration names
// resolves to on-event even when another output in the same block was declared
// on-detect, and its leading edge keeps the scheduled time.
TEST(PulseFilterStyleSim, DefaultStyleIsOnEventForUndeclaredOutput) {
  SimFixture f;
  SpecifyManager mgr;
  LoadPulseStylesFromSource("    pulsestyle_ondetect out;", f, mgr);
  EXPECT_EQ(mgr.ResolvePulseStyle("other"), PulseStyle::kOnEvent);
  EXPECT_EQ(FilteredPulseLeadingXTime(mgr.ResolvePulseStyle("other"),
                                      /*detect_time=*/10,
                                      /*scheduled_leading_time=*/14),
            14u);
}

// list_of_path_outputs form: a single pulsestyle_ondetect declaration listing
// several outputs selects the style for every output it names.
TEST(PulseFilterStyleSim, MultipleOutputsShareDeclaredStyle) {
  SimFixture f;
  SpecifyManager mgr;
  LoadPulseStylesFromSource("    pulsestyle_ondetect a, b, c;", f, mgr);
  EXPECT_EQ(mgr.ResolvePulseStyle("a"), PulseStyle::kOnDetect);
  EXPECT_EQ(mgr.ResolvePulseStyle("b"), PulseStyle::kOnDetect);
  EXPECT_EQ(mgr.ResolvePulseStyle("c"), PulseStyle::kOnDetect);
}

// The pulse-style invocation option takes precedence over a specify block pulse
// style declaration: an output declared on-detect in source resolves to the
// globally selected on-event once the invocation option is present.
TEST(PulseFilterStyleSim, InvocationOptionOverridesSpecifyBlock) {
  SimFixture f;
  SpecifyManager mgr;
  LoadPulseStylesFromSource("    pulsestyle_ondetect out;", f, mgr);
  ASSERT_EQ(mgr.ResolvePulseStyle("out"), PulseStyle::kOnDetect);
  mgr.SetGlobalPulseStyle(PulseStyle::kOnEvent);
  EXPECT_EQ(mgr.ResolvePulseStyle("out"), PulseStyle::kOnEvent);
  EXPECT_EQ(FilteredPulseLeadingXTime(mgr.ResolvePulseStyle("out"),
                                      /*detect_time=*/10,
                                      /*scheduled_leading_time=*/14),
            14u);
}

// The default filtering style is a property of a fresh manager, independent of
// any source: any output resolves to on-event when nothing has been declared or
// selected globally.
TEST(PulseFilterStyleSim, DefaultManagerResolvesOnEvent) {
  SpecifyManager mgr;
  EXPECT_EQ(mgr.ResolvePulseStyle("anything"), PulseStyle::kOnEvent);
}

// End-to-end through the §30.7 dependency: the on-event/on-detect rule governs
// only a pulse that §30.7's ClassifyPulse actually filters to x, so this test
// produces that precondition from real machinery rather than assuming it. One
// specify block carries both a pulsestyle_ondetect declaration and the module
// path delay for the same output (the pulsestyle precedes the path, so it is
// legal per §30.7.4.1). The path delay is built from the real (a => y) source,
// §30.7.2 global scaling opens an x-filter window, §30.7's ClassifyPulse
// confirms a mid-width pulse is filtered to x, and only then does §30.7.4.1's
// on-detect style advance that filtered pulse's leading edge to the detection
// time — contrasted against the scheduled time the default on-event would keep.
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
  ASSERT_EQ(pd.delays[0], 7u);  // rise delay produced by the real source

  // §30.7.2: scale the limits so the rise transition has an x-filter window of
  // reject 2 (30% of 7) up to error 7 (100% of 7).
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/30, /*error_pct=*/100);
  ASSERT_EQ(pd.reject_limit[0], 2u);
  ASSERT_EQ(pd.error_limit[0], 7u);

  // §30.7: a width-4 pulse falls inside [reject, error), so it is filtered to
  // x.
  ASSERT_EQ(
      ClassifyPulse(/*pulse_width=*/4, pd.reject_limit[0], pd.error_limit[0]),
      PulseClassification::kForceX);

  // §30.7.4.1: the pulsestyle_ondetect declaration makes the leading edge of
  // the x-filtered pulse transition at detection time, not the scheduled time.
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

}  // namespace
