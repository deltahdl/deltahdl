#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_specify_path_decl.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// §30.7.2 controls the pulse limits through GLOBAL invocation-option
// percentages, not through source syntax: the percentages are integers supplied
// to the tool, while the value they scale — the module path transition delay —
// is produced by the §30.5.1 machinery. The scaling rule therefore CONSUMES a
// real delay, so every test below builds that delay from actual
// `(a => y) = ...;` specify source, elaborates it, and runs
// BuildPathDelayFromDecl rather than hand-setting a delays[] array. The one
// exception is the default-percentage fact, which is a property of the
// manager's initial state and involves no delay input.

// Builds the runtime PathDelay for the sole module path in `specify_body`,
// driving the full parse/elaborate/lower pipeline so the delay slots hold the
// values the §30.5.1 syntax produced.
PathDelay BuildDelayFromSource(const std::string& specify_body, SimFixture& f) {
  auto c = ElaboratePathDecl("input a, output y", specify_body, f);
  EXPECT_NE(c.decl, nullptr);
  EXPECT_NE(c.design, nullptr);
  LowerAndRun(c.design, f);
  PathDelay pd = BuildPathDelayFromDecl(*c.decl, f.ctx, f.arena);
  InitDefaultPulseLimits(pd);
  return pd;
}

// Claim 3: with both percentages at their 100% default, global scaling leaves
// each slot's reject and error limit equal to the parsed delay — the full
// inertial default behavior of §30.7.
TEST(GlobalPulseLimitScaling, HundredPercentEqualsInertialDefault) {
  SimFixture f;
  PathDelay pd = BuildDelayFromSource("    (a => y) = (7, 9);", f);
  ASSERT_EQ(pd.delays[0], 7u);
  ASSERT_EQ(pd.delays[1], 9u);
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/100, /*error_pct=*/100);
  EXPECT_EQ(pd.reject_limit[0], 7u);
  EXPECT_EQ(pd.error_limit[0], 7u);
  EXPECT_EQ(pd.reject_limit[1], 9u);
  EXPECT_EQ(pd.error_limit[1], 9u);
}

// Claim 1: the reject and error percentages independently scale the parsed
// delay. A delay of 40 with reject 25% and error 75% yields limits 10 and 30.
TEST(GlobalPulseLimitScaling, PercentagesScaleParsedDelay) {
  SimFixture f;
  PathDelay pd = BuildDelayFromSource("    (a => y) = 40;", f);
  ASSERT_EQ(pd.delays[0], 40u);
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/25, /*error_pct=*/75);
  EXPECT_EQ(pd.reject_limit[0], 10u);
  EXPECT_EQ(pd.error_limit[0], 30u);
}

// Claim 1, input form: a specparam delay (a constant expression per 11.2.1) is
// resolved by §30.5.1 and then scaled by the global percentages just as a
// literal delay is.
TEST(GlobalPulseLimitScaling, SpecparamDelayScaledByPercentages) {
  SimFixture f;
  PathDelay pd =
      BuildDelayFromSource("    specparam d = 80;\n    (a => y) = d;", f);
  ASSERT_EQ(pd.delays[0], 80u);
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/50, /*error_pct=*/100);
  EXPECT_EQ(pd.reject_limit[0], 40u);
  EXPECT_EQ(pd.error_limit[0], 80u);
}

// Claim 2, valid endpoint 0: a 0% percentage is an integer in range and drives
// the corresponding limit to zero.
TEST(GlobalPulseLimitScaling, ZeroPercentProducesZeroLimits) {
  SimFixture f;
  PathDelay pd = BuildDelayFromSource("    (a => y) = 40;", f);
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/0, /*error_pct=*/0);
  EXPECT_EQ(pd.reject_limit[0], 0u);
  EXPECT_EQ(pd.error_limit[0], 0u);
}

// Claim 4 (the error path): it is an error for the error percentage to be
// smaller than the reject percentage; in that case the error percentage is
// raised to equal the reject percentage. Delay 100 with reject 60% and error
// 30% therefore yields both limits at 60, not 30.
TEST(GlobalPulseLimitScaling, ErrorBelowRejectIsClampedUp) {
  SimFixture f;
  PathDelay pd = BuildDelayFromSource("    (a => y) = 100;", f);
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/60, /*error_pct=*/30);
  EXPECT_EQ(pd.reject_limit[0], 60u);
  EXPECT_EQ(pd.error_limit[0], 60u);
}

// Claim 1, per-slot independence: a six-value transition-delay list expands
// across all twelve slots (§30.5.1 Table 30-2); the global percentage scales
// each slot's own delay rather than a single shared value.
TEST(GlobalPulseLimitScaling, PerSlotScalingFromSixDelays) {
  SimFixture f;
  PathDelay pd =
      BuildDelayFromSource("    (a => y) = (10, 20, 30, 40, 50, 60);", f);
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/50, /*error_pct=*/100);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], pd.delays[i] / 2) << "reject slot " << i;
    EXPECT_EQ(pd.error_limit[i], pd.delays[i]) << "error slot " << i;
  }
}

// Claim 1, input form: a min:typ:max path delay. §30.5.1 selects the member for
// the active delay mode (the typical value under the default), and the global
// percentages scale that selected member — here typ 8 at reject 50% and error
// 100% gives limits 4 and 8, derived from 8 rather than the min or max.
TEST(GlobalPulseLimitScaling, MinTypMaxDelayScaledByPercentages) {
  SimFixture f;
  PathDelay pd = BuildDelayFromSource("    (a => y) = 6:8:10;", f);
  ASSERT_EQ(pd.delays[0], 8u);  // typical member selected by §30.5.1
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/50, /*error_pct=*/100);
  EXPECT_EQ(pd.reject_limit[0], 4u);
  EXPECT_EQ(pd.error_limit[0], 8u);
}

// Claim 1, input form: a full twelve-value transition-delay list, which §30.5.1
// places verbatim into the twelve slots. The global percentage scales each
// slot's own value, confirming the scaling is applied uniformly across every
// distinct per-slot delay.
TEST(GlobalPulseLimitScaling, TwelveValueDelayScaledPerSlot) {
  SimFixture f;
  PathDelay pd = BuildDelayFromSource(
      "    (a => y) = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);", f);
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/100, /*error_pct=*/100);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], pd.delays[i]) << "reject slot " << i;
    EXPECT_EQ(pd.error_limit[i], pd.delays[i]) << "error slot " << i;
  }
}

// Claim 1: global scaling only touches the pulse limits; the propagation delays
// themselves are untouched.
TEST(GlobalPulseLimitScaling, PropagationDelaysPreserved) {
  SimFixture f;
  PathDelay pd = BuildDelayFromSource("    (a => y) = 40;", f);
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/50, /*error_pct=*/70);
  for (int i = 0; i < 12; ++i) EXPECT_EQ(pd.delays[i], 40u);
}

// Claim 5: when both PATHPULSE$ (§30.7.1) and global percentages are present,
// the PATHPULSE$ values take precedence. After global scaling sets the limits,
// a path-specific PATHPULSE$ override replaces them.
TEST(GlobalPulseLimitScaling, PathpulseOverridesGlobalLimits) {
  SimFixture f;
  PathDelay pd = BuildDelayFromSource("    (a => y) = 100;", f);
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/50, /*error_pct=*/80);
  ApplyPulseControlOverride(pd, /*reject=*/5, /*has_error=*/true, /*error=*/9);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 5u);
    EXPECT_EQ(pd.error_limit[i], 9u);
  }
}

// Claim 5, end-to-end through the §30.7.1 dependency: a PATHPULSE$ specparam
// written in real specify source takes precedence over the globally-scaled
// limits. The path delay is scaled by the global percentages first, then the
// production PATHPULSE$ resolver (ResolvePulseControlSpecparams) overrides the
// named path, so the limits observed on the manager are the PATHPULSE$ values,
// not delay*pct/100.
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
  std::vector<PulseControlSpecparam> specs;
  for (auto* item : cu->modules.back()->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      if (si->kind == SpecifyItemKind::kPathDecl) {
        PathDelay pd = BuildPathDelayFromDecl(si->path, f.ctx, f.arena);
        InitDefaultPulseLimits(pd);
        // Global invocation-option scaling is applied before PATHPULSE$: at 50%
        // reject / 80% error a delay of 100 would yield limits 50 and 80.
        ApplyGlobalPulseLimits(pd, /*reject_pct=*/50, /*error_pct=*/80);
        mgr.AddPathDelay(pd);
      } else if (si->kind == SpecifyItemKind::kSpecparam && si->is_pathpulse) {
        PulseControlSpecparam s;
        s.input = si->pathpulse_input;
        s.output = si->pathpulse_output;
        s.reject = EvalExpr(si->pathpulse_reject, f.ctx, f.arena).ToUint64();
        s.has_error = si->pathpulse_error != nullptr;
        if (s.has_error) {
          s.error = EvalExpr(si->pathpulse_error, f.ctx, f.arena).ToUint64();
        }
        specs.push_back(s);
      }
    }
  }
  mgr.ResolvePulseControlSpecparams(specs);

  const PathDelay* p = nullptr;
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.src_port == "clk" && pd.dst_port == "q") p = &pd;
  }
  ASSERT_NE(p, nullptr);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(p->reject_limit[i], 5u);  // PATHPULSE$ reject wins over 50
    EXPECT_EQ(p->error_limit[i], 9u);   // PATHPULSE$ error wins over 80
  }
}

// Claim 3 (the default fact): when neither global invocation option is present,
// both percentages default to 100%. This is a property of the manager's initial
// state, independent of any delay, so it is observed directly on
// SpecifyManager.
TEST(GlobalPulseLimitScaling, DefaultGlobalPercentagesAreHundred) {
  SpecifyManager mgr;
  EXPECT_EQ(mgr.RejectPulseLimitPercent(), 100u);
  EXPECT_EQ(mgr.ErrorPulseLimitPercent(), 100u);
}

}  // namespace
