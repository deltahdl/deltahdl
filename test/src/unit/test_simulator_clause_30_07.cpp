#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

TEST(PulseFiltering, PulseAtErrorLimitPropagates) {
  EXPECT_EQ(ClassifyPulse(7, 3, 7), PulseClassification::kPropagate);
}

TEST(PulseFiltering, PulseAtRejectLimitForcesXWhenErrorHigher) {
  EXPECT_EQ(ClassifyPulse(3, 3, 7), PulseClassification::kForceX);
}

TEST(PulseFiltering, PulseJustBelowErrorLimitForcesX) {
  EXPECT_EQ(ClassifyPulse(6, 3, 7), PulseClassification::kForceX);
}

TEST(PulseFiltering, PulseBelowRejectLimitIsRejected) {
  EXPECT_EQ(ClassifyPulse(2, 3, 7), PulseClassification::kReject);
}

TEST(PulseFiltering, ClassifierProducesOneOfThreeCategories) {
  PulseClassification a = ClassifyPulse(1, 3, 7);
  PulseClassification b = ClassifyPulse(5, 3, 7);
  PulseClassification c = ClassifyPulse(9, 3, 7);
  EXPECT_EQ(a, PulseClassification::kReject);
  EXPECT_EQ(b, PulseClassification::kForceX);
  EXPECT_EQ(c, PulseClassification::kPropagate);
}

// --- §30.7 head text: the default pulse limits are DERIVED from a module path
// transition delay, which the §30.5/§30.5.1 syntax produces. The classification
// rule (ClassifyPulse) is a pure function of three integers, so it stays a
// synthetic single-stage test above; but the default-limit rule consumes a real
// delay, so it is re-observed here on a PathDelay parsed and elaborated from
// actual `(a => y) = (rise, fall);` source rather than a hand-set delays[]
// array.

// Parses and elaborates a module with the given ports and specify body, then
// returns the first module path declaration together with its design so the
// delay expressions can be evaluated in the simulation context.
struct ElaboratedPathDecl {
  const SpecifyPathDecl* decl = nullptr;
  RtlirDesign* design = nullptr;
};

ElaboratedPathDecl ElaboratePathDecl(const std::string& port_header,
                                     const std::string& specify_body,
                                     SimFixture& f) {
  std::string code = "module t(" + port_header + ");\n  specify\n" +
                     specify_body + "\n  endspecify\nendmodule\n";
  auto fid = f.mgr.AddFile("<test>", code);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  ElaboratedPathDecl out;
  out.design = elab.Elaborate(cu->modules.back()->name);
  for (auto* mod : cu->modules) {
    for (auto* item : mod->items) {
      if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
      for (auto* si : item->specify_items) {
        if (si->kind == SpecifyItemKind::kPathDecl) {
          out.decl = &si->path;
          return out;
        }
      }
    }
  }
  return out;
}

// Figure 30-5: a buffer path with rise delay 7 and fall delay 9. By default the
// reject and error limits equal the transition delay, so each limit array slot
// mirrors the delay produced by the parsed source.
TEST(PulseFilteringFromSource, DefaultLimitsMirrorParsedTransitionDelays) {
  SimFixture f;
  auto c = ElaboratePathDecl("input a, output y", "    (a => y) = (7, 9);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  LowerAndRun(c.design, f);
  PathDelay pd = BuildPathDelayFromDecl(*c.decl, f.ctx, f.arena);
  ASSERT_EQ(pd.delays[0], 7u);
  ASSERT_EQ(pd.delays[1], 9u);
  InitDefaultPulseLimits(pd);
  EXPECT_EQ(pd.reject_limit[0], 7u);
  EXPECT_EQ(pd.error_limit[0], 7u);
  EXPECT_EQ(pd.reject_limit[1], 9u);
  EXPECT_EQ(pd.error_limit[1], 9u);
}

// Figure 30-5: a pulse of width 2 is narrower than the reject limit derived
// from the rise delay of 7, so with default limits it is rejected and no pulse
// emerges.
TEST(PulseFilteringFromSource, NarrowPulseRejectedUnderDerivedDefaults) {
  SimFixture f;
  auto c = ElaboratePathDecl("input a, output y", "    (a => y) = (7, 9);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  LowerAndRun(c.design, f);
  PathDelay pd = BuildPathDelayFromDecl(*c.decl, f.ctx, f.arena);
  InitDefaultPulseLimits(pd);
  EXPECT_EQ(ClassifyPulse(2, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kReject);
  // A pulse as wide as the derived delay passes unfiltered.
  EXPECT_EQ(ClassifyPulse(7, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kPropagate);
}

// The limits that govern filtering are those of the transition forming the
// pulse's trailing edge: width 8 propagates against the rise slot (limit 7) but
// is rejected against the fall slot (limit 9), both derived from real source.
TEST(PulseFilteringFromSource, TrailingEdgeDerivedLimitsGovern) {
  SimFixture f;
  auto c = ElaboratePathDecl("input a, output y", "    (a => y) = (7, 9);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  LowerAndRun(c.design, f);
  PathDelay pd = BuildPathDelayFromDecl(*c.decl, f.ctx, f.arena);
  InitDefaultPulseLimits(pd);
  EXPECT_EQ(ClassifyPulse(8, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kPropagate);
  EXPECT_EQ(ClassifyPulse(8, pd.reject_limit[1], pd.error_limit[1]),
            PulseClassification::kReject);
}

// A path delay supplied through a specparam (a constant expression per 11.2.1)
// still yields default limits equal to the resolved delay.
TEST(PulseFilteringFromSource, SpecparamDelayDrivesDefaultLimits) {
  SimFixture f;
  auto c = ElaboratePathDecl("input a, output y",
                             "    specparam d = 6;\n    (a => y) = d;", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  LowerAndRun(c.design, f);
  PathDelay pd = BuildPathDelayFromDecl(*c.decl, f.ctx, f.arena);
  ASSERT_EQ(pd.delays[0], 6u);
  InitDefaultPulseLimits(pd);
  EXPECT_EQ(pd.reject_limit[0], 6u);
  EXPECT_EQ(pd.error_limit[0], 6u);
  EXPECT_EQ(ClassifyPulse(3, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kReject);
}

// Input form: a min:typ:max path delay. The selected member (the typical value
// under the default delay mode) becomes the delay, and the default pulse limits
// mirror that selected member rather than the min or max.
TEST(PulseFilteringFromSource, MinTypMaxDelaySelectsDefaultLimit) {
  SimFixture f;
  auto c = ElaboratePathDecl("input a, output y", "    (a => y) = 6:8:10;", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  LowerAndRun(c.design, f);
  PathDelay pd = BuildPathDelayFromDecl(*c.decl, f.ctx, f.arena);
  ASSERT_EQ(pd.delays[0], 8u);  // typical member selected
  InitDefaultPulseLimits(pd);
  EXPECT_EQ(pd.reject_limit[0], 8u);
  EXPECT_EQ(pd.error_limit[0], 8u);
  // A pulse narrower than the selected delay is rejected; one as wide passes.
  EXPECT_EQ(ClassifyPulse(7, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kReject);
  EXPECT_EQ(ClassifyPulse(8, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kPropagate);
}

// Input form: a six-value transition-delay list, which the §30.5.1 machinery
// expands across all twelve transition slots. The default pulse limits must
// mirror the resolved delay in EVERY slot, not just the first two.
TEST(PulseFilteringFromSource, DefaultLimitsMirrorEverySlotFromSixDelays) {
  SimFixture f;
  auto c = ElaboratePathDecl("input a, output y",
                             "    (a => y) = (1, 2, 3, 4, 5, 6);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  LowerAndRun(c.design, f);
  PathDelay pd = BuildPathDelayFromDecl(*c.decl, f.ctx, f.arena);
  InitDefaultPulseLimits(pd);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], pd.delays[i]) << "reject slot " << i;
    EXPECT_EQ(pd.error_limit[i], pd.delays[i]) << "error slot " << i;
  }
}

// Negative/degenerate form: a delay that resolves negative is clamped to zero
// by the §30.5.1 dependency, so the default limits are zero and filtering is
// effectively disabled — every pulse width propagates.
TEST(PulseFilteringFromSource, ClampedZeroDelayDisablesFiltering) {
  SimFixture f;
  auto c = ElaboratePathDecl("input a, output y", "    (a => y) = -4;", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  LowerAndRun(c.design, f);
  PathDelay pd = BuildPathDelayFromDecl(*c.decl, f.ctx, f.arena);
  ASSERT_EQ(pd.delays[0], 0u);
  InitDefaultPulseLimits(pd);
  EXPECT_EQ(pd.reject_limit[0], 0u);
  EXPECT_EQ(pd.error_limit[0], 0u);
  EXPECT_EQ(ClassifyPulse(0, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kPropagate);
  EXPECT_EQ(ClassifyPulse(1, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kPropagate);
}

}  // namespace
