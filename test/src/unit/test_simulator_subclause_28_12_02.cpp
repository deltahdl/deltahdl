// Unit tests for IEEE 1800-2023 §28.12.2, "Ambiguous strengths: sources and
// combinations".
//
// The last group, AmbiguousStrengthModelCombine, calls CombineAmbiguous in
// lib/cpp/test_models/model_strength.h. Issue #3417 found that function called
// from nowhere in the repository, so the claim it states about §28.12.2 was
// evaluated by no run. Its five cases assert the result the clause states:
// Figure 28-10's 35x, Figure 28-14's 56x, Figure 28-15's strong x, the range
// covering two value-H components, and the range covering two value-1
// components that reach no lower than We1.
//
// The last of the five is the case issue #3423 records. It is the only one
// whose result holds no high-impedance level, the other four each answering a
// range whose strength0_lo and strength1_lo fields are high impedance. Those
// four therefore passed while CombineAmbiguous read strength0_hi and
// strength1_hi alone and left every result's two _lo fields at high impedance,
// and their expectations are unchanged: Figure 28-10, Figure 28-14 and Figure
// 28-15 each draw a range that does reach high impedance.
//
// The earlier groups resolve a Net, classify a NetStrength, call the
// simulator's own CombineAmbiguousStrength, and run drive-strength source end
// to end.

#include <gtest/gtest.h>

#include "common/arena.h"
#include "fixture_simulator.h"
#include "helpers_net_strength.h"
#include "model_strength.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StrengthResolution, EqualStrengthConflictPerBit) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 8);
  Net& net = sn.net;

  AddDriver(arena, net, 8, 0xF0, Strength::kStrong);
  AddDriver(arena, net, 8, 0x0F, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(sn.var->value.words[0].aval & 0xFFu, 0xFFu);  // all bits x
  EXPECT_EQ(sn.var->value.words[0].bval & 0xFFu, 0xFFu);
}

TEST(StrengthResolution, EqualStrengthPartialConflictPerBit) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 4);
  Net& net = sn.net;

  AddDriver(arena, net, 4, 0b1100, Strength::kStrong);
  AddDriver(arena, net, 4, 0b1010, Strength::kStrong);
  net.Resolve(arena);

  // bit3=1, bit2=x, bit1=x, bit0=0. Under Convention A an x bit sets aval, so
  // aval = 0b1110 (the known 1 at bit3 plus the two x bits), bval = 0b0110.
  EXPECT_EQ(sn.var->value.words[0].aval & 0xFu, 0b1110u);
  EXPECT_EQ(sn.var->value.words[0].bval & 0xFu, 0b0110u);
}

TEST(StrengthResolution, EqualStrengthConflictOnTriNetPopulatesAmbiguous) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1, NetType::kTri);
  Net& net = sn.net;

  AddDriver(arena, net, 1, 0, Strength::kStrong);
  AddDriver(arena, net, 1, 1, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(sn.var->value.words[0].aval & 1u, 1u);  // x = (aval=1, bval=1)
  EXPECT_EQ(sn.var->value.words[0].bval & 1u, 1u);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_TRUE(net.resolved_strength.IsAmbiguous());
}

// Known-value-with-multi-level classification: only the value side carries
// a non-singleton range; the opposite side stays HiZ.
TEST(AmbiguousStrengthClass, KnownValueMultiLevelIsAmbiguous) {
  NetStrength ns;
  ns.s1_hi = Strength::kStrong;
  ns.s1_lo = Strength::kWeak;
  EXPECT_TRUE(ns.IsAmbiguous());
  EXPECT_EQ(ns.s0_hi, Strength::kHighz);
  EXPECT_EQ(ns.s0_lo, Strength::kHighz);
}

// X-value classification: levels straddle both halves of the scale.
TEST(AmbiguousStrengthClass, XValueRangesOnBothSidesIsAmbiguous) {
  NetStrength ns;
  ns.s0_hi = Strength::kStrong;
  ns.s0_lo = Strength::kPull;
  ns.s1_hi = Strength::kStrong;
  ns.s1_lo = Strength::kPull;
  EXPECT_TRUE(ns.IsAmbiguous());
  EXPECT_NE(ns.s0_hi, Strength::kHighz);
  EXPECT_NE(ns.s1_hi, Strength::kHighz);
}

// L-value classification: HiZ joined with a range in the strength0 part.
TEST(AmbiguousStrengthClass, LValueIsHighZJoinedWithStrengthZeroRange) {
  NetStrength ns;
  ns.s0_hi = Strength::kStrong;
  ns.s0_lo = Strength::kHighz;
  EXPECT_TRUE(ns.IsAmbiguous());
  EXPECT_EQ(ns.s1_hi, Strength::kHighz);
  EXPECT_EQ(ns.s1_lo, Strength::kHighz);
}

// H-value classification: HiZ joined with a range in the strength1 part.
TEST(AmbiguousStrengthClass, HValueIsHighZJoinedWithStrengthOneRange) {
  NetStrength ns;
  ns.s1_hi = Strength::kStrong;
  ns.s1_lo = Strength::kHighz;
  EXPECT_TRUE(ns.IsAmbiguous());
  EXPECT_EQ(ns.s0_hi, Strength::kHighz);
  EXPECT_EQ(ns.s0_lo, Strength::kHighz);
}

// COMB-2 + COMB-3 via production CombineAmbiguousStrength: per-side hi widens
// to the maximum and per-side lo shrinks to the minimum, so the result's
// range on each side covers the ranges of both inputs.
TEST(AmbiguousNetStrengthCombine, WidensPerSideToCoverBothInputRanges) {
  NetStrength a;
  a.s0_hi = Strength::kWeak;
  a.s0_lo = Strength::kSmall;
  a.s1_hi = Strength::kPull;
  a.s1_lo = Strength::kWeak;
  NetStrength b;
  b.s0_hi = Strength::kPull;
  b.s0_lo = Strength::kMedium;
  b.s1_hi = Strength::kStrong;
  b.s1_lo = Strength::kMedium;

  NetStrength r = CombineAmbiguousStrength(a, b);

  EXPECT_EQ(r.s0_hi, Strength::kPull);
  EXPECT_EQ(r.s0_lo, Strength::kSmall);
  EXPECT_EQ(r.s1_hi, Strength::kStrong);
  EXPECT_EQ(r.s1_lo, Strength::kMedium);
  EXPECT_TRUE(r.IsAmbiguous());
}

// COMB-2: combining two X-value (CLA-2) signals through production code
// yields a result that is still ambiguous on both sides.
TEST(AmbiguousNetStrengthCombine, XValueRangesProduceWiderXValueRange) {
  NetStrength a;
  a.s0_hi = Strength::kWeak;
  a.s0_lo = Strength::kSmall;
  a.s1_hi = Strength::kWeak;
  a.s1_lo = Strength::kSmall;
  NetStrength b;
  b.s0_hi = Strength::kStrong;
  b.s0_lo = Strength::kPull;
  b.s1_hi = Strength::kStrong;
  b.s1_lo = Strength::kPull;

  NetStrength r = CombineAmbiguousStrength(a, b);

  EXPECT_EQ(r.s0_hi, Strength::kStrong);
  EXPECT_EQ(r.s0_lo, Strength::kSmall);
  EXPECT_EQ(r.s1_hi, Strength::kStrong);
  EXPECT_EQ(r.s1_lo, Strength::kSmall);
  EXPECT_TRUE(r.IsAmbiguous());
}

// COMB-3: an L (CLA-3) and an H (CLA-4) input contribute their levels on
// opposite halves of the scale; the union covers both halves.
TEST(AmbiguousNetStrengthCombine, LAndHCombineToTwoSidedRange) {
  NetStrength l_signal;
  l_signal.s0_hi = Strength::kPull;
  l_signal.s0_lo = Strength::kHighz;
  NetStrength h_signal;
  h_signal.s1_hi = Strength::kPull;
  h_signal.s1_lo = Strength::kHighz;

  NetStrength r = CombineAmbiguousStrength(l_signal, h_signal);

  EXPECT_EQ(r.s0_hi, Strength::kPull);
  EXPECT_EQ(r.s0_lo, Strength::kHighz);
  EXPECT_EQ(r.s1_hi, Strength::kPull);
  EXPECT_EQ(r.s1_lo, Strength::kHighz);
  EXPECT_TRUE(r.IsAmbiguous());
}

// Idempotency edge case for COMB-3: combining an ambiguous signal with
// itself returns an identical NetStrength. Per-side max/min on equal inputs
// collapses to the input.
TEST(AmbiguousNetStrengthCombine, SelfCombinationIsIdempotent) {
  NetStrength ns;
  ns.s0_hi = Strength::kPull;
  ns.s0_lo = Strength::kWeak;
  ns.s1_hi = Strength::kStrong;
  ns.s1_lo = Strength::kMedium;

  NetStrength r = CombineAmbiguousStrength(ns, ns);

  EXPECT_EQ(r.s0_hi, ns.s0_hi);
  EXPECT_EQ(r.s0_lo, ns.s0_lo);
  EXPECT_EQ(r.s1_hi, ns.s1_hi);
  EXPECT_EQ(r.s1_lo, ns.s1_lo);
  EXPECT_TRUE(r.IsAmbiguous());
}

// Edge case for COMB-3: combining an ambiguous signal whose lo is non-HiZ
// with a default (all-HiZ) NetStrength pushes the per-side lo down to HiZ
// while preserving the per-side hi. HiZ acts as the bottom of the scale
// for the min that defines the lo bound.
TEST(AmbiguousNetStrengthCombine, CombiningWithDefaultStretchesLoToHighz) {
  NetStrength narrow;
  narrow.s1_hi = Strength::kPull;
  narrow.s1_lo = Strength::kWeak;
  NetStrength empty;

  NetStrength r = CombineAmbiguousStrength(narrow, empty);

  EXPECT_EQ(r.s1_hi, Strength::kPull);
  EXPECT_EQ(r.s1_lo, Strength::kHighz);
  EXPECT_EQ(r.s0_hi, Strength::kHighz);
  EXPECT_EQ(r.s0_lo, Strength::kHighz);
}

// --- Full-pipeline observation of §28.12.2 Claim 1 --------------------------
// When two signals of equal strength and opposite value combine, the result is
// value x carrying the strength levels of both signals plus all the smaller
// strength levels (Figure 28-4 / Figure 28-5). §28.12.1 explicitly delegates
// this unlike-value/same-strength case here. The competing drivers are produced
// from real drive-strength source (the machinery of §28.11), elaborated,
// lowered, and run, so the resolved value and the ambiguous resolved strength
// are observed exactly as the production resolver computes them -- rather than
// from a hand-assembled Net or a test-model combiner.

// Elaborates, lowers, and runs `src`, then returns the settled net named "w".
static Net* RunAndFindNetW(SimFixture& f, const char* src) {
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return nullptr;
  LowerAndRun(design, f);
  return f.ctx.FindNet("w");
}

// Checks the settled net holds x and its resolved strength spans `hi` down to
// HiZ on both sides of the scale, which is what the standard's "all the
// smaller strength levels" clause makes an equal-strength conflict produce.
static void ExpectXSpanningDownToHighz(SimFixture& f, Net* net, Strength hi) {
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 1u, 1u);  // x = (aval=1, bval=1)
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
  EXPECT_EQ(net->resolved_strength.s0_hi, hi);
  EXPECT_EQ(net->resolved_strength.s1_hi, hi);
  EXPECT_EQ(net->resolved_strength.s0_lo, Strength::kHighz);
  EXPECT_EQ(net->resolved_strength.s1_lo, Strength::kHighz);
  EXPECT_TRUE(net->resolved_strength.IsAmbiguous());
}

// Figure 28-4 exactly: a weak 1 and a weak 0 driving one wire settle to a weak
// x. The resolved strength is ambiguous, its high bound the shared weak level
// on both sides and its low bound HiZ -- i.e. weak plus every smaller level.
TEST(StrengthResolutionPipeline, EqualWeakOppositeValueYieldsWeakX) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wire w;\n"
                            "  assign (weak0, weak1) w = 1'b1;\n"
                            "  assign (weak0, weak1) w = 1'b0;\n"
                            "endmodule\n");
  ExpectXSpanningDownToHighz(f, net, Strength::kWeak);
}

// The "all the smaller strength levels" clause made explicit at strong: a
// strong 1 opposing a strong 0 yields x whose range spans strong down to HiZ
// on both sides of the scale, not just the strong endpoint.
TEST(StrengthResolutionPipeline,
     EqualStrongOppositeValueSpansAllSmallerLevels) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wire w;\n"
                            "  assign (strong0, strong1) w = 1'b1;\n"
                            "  assign (strong0, strong1) w = 1'b0;\n"
                            "endmodule\n");
  ExpectXSpanningDownToHighz(f, net, Strength::kStrong);
}

// Input-form coverage: the equal-strength opposite-value drivers originate from
// gate primitive outputs (§28.4 gate syntax) rather than continuous
// assignments. §28.12.2's rule resolves the drivers regardless of how they are
// produced, so the same weak x results.
TEST(StrengthResolutionPipeline, EqualStrengthConflictFromGateOutputs) {
  SimFixture f;
  Net* net = RunAndFindNetW(
      f,
      "module t;\n"
      "  wire w;\n"
      "  wire a = 1'b1, b = 1'b1;\n"         // and -> 1
      "  wire c = 1'b0, d = 1'b1;\n"         // and -> 0
      "  and (weak0, weak1) g0(w, a, b);\n"  // weak-strength 1 driver
      "  and (weak0, weak1) g1(w, c, d);\n"  // weak-strength 0 driver
      "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 1u, 1u);  // x
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
  EXPECT_EQ(net->resolved_strength.s0_hi, Strength::kWeak);
  EXPECT_EQ(net->resolved_strength.s1_hi, Strength::kWeak);
  EXPECT_TRUE(net->resolved_strength.IsAmbiguous());
}

// Input-form coverage: one of the conflicting drivers is produced by a
// net-declaration assignment (§6.10 / §28.11) -- a continuous driver in a
// different syntactic position than a standalone `assign`. It competes with an
// opposite-value cont-assign driver of equal strength, and §28.12.2's rule
// resolves the two into a strong x with a range down to HiZ.
TEST(StrengthResolutionPipeline, EqualStrengthConflictFromNetDeclInitializer) {
  SimFixture f;
  Net* net =
      RunAndFindNetW(f,
                     "module t;\n"
                     "  wire (strong0, strong1) w = 1'b1;\n"    // net-decl 1
                     "  assign (strong0, strong1) w = 1'b0;\n"  // 0 driver
                     "endmodule\n");
  ExpectXSpanningDownToHighz(f, net, Strength::kStrong);
}

// Input-form coverage: a vector operand driven end to end. §28.12.2's rule is
// applied independently per bit, so on a multi-bit net each bit is resolved on
// its own -- conflicting bits become x while agreeing bits keep their value.
// The competing vector drivers come from real drive-strength cont-assign source
// rather than a hand-built Net.
TEST(StrengthResolutionPipeline, EqualStrengthConflictVectorResolvesPerBit) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wire [3:0] w;\n"
                            "  assign (strong0, strong1) w = 4'b1100;\n"
                            "  assign (strong0, strong1) w = 4'b1010;\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  // bit3: 1 vs 1 -> 1; bit2: 1 vs 0 -> x; bit1: 0 vs 1 -> x; bit0: 0 vs 0 -> 0.
  // Convention A: an x bit sets aval, so aval = 0b1110, bval = 0b0110.
  EXPECT_EQ(var->value.words[0].aval & 0xFu, 0b1110u);
  EXPECT_EQ(var->value.words[0].bval & 0xFu, 0b0110u);
}

// --- §28.12.2 against CombineAmbiguous in model_strength.h -----------------
// Each case below calls CombineAmbiguous, the model of §28.12.2 that
// lib/cpp/test_models/model_strength.h states, and asserts the fields §28.12.2
// decides. Figure 28-2's scale numbers the levels Su0 7 down to HiZ0 0 and HiZ1
// 0 up to Su1 7, so StrengthLevel::kWeak is the digit 3 and
// StrengthLevel::kPull the digit 5 that the clause's two-digit strength numbers
// name.

// A signal whose strength levels lie in the strength0 part of Figure 28-2's
// scale, spanning `lo` through `hi`. §28.12.2 classifies it as a signal with a
// value L when `lo` is high impedance, and as a signal with a known value and
// multiple strength levels otherwise.
StrengthSignal Strength0Range(StrengthLevel lo, StrengthLevel hi) {
  StrengthSignal s;
  s.value = Val4::kV0;
  s.strength0_lo = lo;
  s.strength0_hi = hi;
  return s;
}

// A signal whose strength levels lie in the strength1 part of Figure 28-2's
// scale, spanning `lo` through `hi`. §28.12.2 classifies it as a signal with a
// value H when `lo` is high impedance, and as a signal with a known value and
// multiple strength levels otherwise.
StrengthSignal Strength1Range(StrengthLevel lo, StrengthLevel hi) {
  StrengthSignal s;
  s.value = Val4::kV1;
  s.strength1_lo = lo;
  s.strength1_hi = hi;
  return s;
}

// Figure 28-9's worked example: the pull H of Figure 28-7's shape and the weak
// L of Figure 28-8's shape combine into the 35x signal Figure 28-10 draws.
// "In Figure 28-9, the combination of signals of ambiguous strengths produces a
// range that includes the extremes of the signals and all the strengths between
// them, as described in Figure 28-10."
TEST(AmbiguousStrengthModelCombine, PullHAndWeakLGiveThreeFiveX) {
  StrengthSignal pull_h =
      Strength1Range(StrengthLevel::kHighz, StrengthLevel::kPull);
  StrengthSignal weak_l =
      Strength0Range(StrengthLevel::kHighz, StrengthLevel::kWeak);

  StrengthSignal r = CombineAmbiguous(pull_h, weak_l);

  // "The result is a value x because its range includes the values 1 and 0."
  EXPECT_EQ(r.value, Val4::kX);
  // "The number 35, which precedes the x, is a concatenation of two digits. The
  // first is the digit 3, which corresponds to the highest strength0 level for
  // the result. The second digit, 5, corresponds to the highest strength1 level
  // for the result."
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kWeak);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kPull);
  // Figure 28-10 draws the range from We0 through HiZ0 and HiZ1 up to Pu1, so
  // high impedance is the low end on both sides.
  EXPECT_EQ(r.strength0_lo, StrengthLevel::kHighz);
  EXPECT_EQ(r.strength1_lo, StrengthLevel::kHighz);
}

// Figure 28-11's worked example: the two switch-network signals combine into
// the 56x signal Figure 28-14 draws. "When the signals from the upper and lower
// configurations in Figure 28-11 combine, the result is an unknown with a range
// (56x) determined by the extremes of the two signals shown in Figure 28-14."
// Neither component reaches high impedance, Figure 28-12 drawing the upper
// signal 651 as Pu1 through St1 and Figure 28-13 drawing the lower signal 530
// as We0 through Pu0.
TEST(AmbiguousStrengthModelCombine, SwitchNetworkRangesGiveFiveSixX) {
  StrengthSignal upper =
      Strength1Range(StrengthLevel::kPull, StrengthLevel::kStrong);
  StrengthSignal lower =
      Strength0Range(StrengthLevel::kWeak, StrengthLevel::kPull);

  StrengthSignal r = CombineAmbiguous(upper, lower);

  // "The result is a value x because its range includes the values 1 and 0."
  EXPECT_EQ(r.value, Val4::kX);
  // The 5 of 56x is the highest strength0 level and the 6 is the highest
  // strength1 level, which are the Pu0 and St1 extremes Figure 28-14 draws.
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kPull);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kStrong);
  // Figure 28-14 draws one range from Pu0 up to St1, so it holds every level
  // between them and reaches high impedance on both sides -- even though
  // Figure 28-12's and Figure 28-13's components each stop short of it.
  EXPECT_EQ(r.strength0_lo, StrengthLevel::kHighz);
  EXPECT_EQ(r.strength1_lo, StrengthLevel::kHighz);
}

// Figure 28-15's worked example: raising the lower component's extreme to
// strong raises the result's strength0 extreme with it. "In Figure 28-11,
// replacing the pulldown in the lower configuration with a supply0 would change
// the range of the result to the range (Stx) described in Figure 28-15." "The
// range in Figure 28-15 is strong x because it is unknown and the extremes of
// both its components are strong. The extreme of the output of the lower
// configuration is strong because the lower pmos reduces the strength of the
// supply0 signal." The substitution moves only that extreme, so the lower
// component keeps the We0 low end Figure 28-13 draws.
TEST(AmbiguousStrengthModelCombine, StrongExtremesGiveStrongX) {
  StrengthSignal upper =
      Strength1Range(StrengthLevel::kPull, StrengthLevel::kStrong);
  StrengthSignal lower =
      Strength0Range(StrengthLevel::kWeak, StrengthLevel::kStrong);

  StrengthSignal r = CombineAmbiguous(upper, lower);

  // "The result is a value x because its range includes the values 1 and 0."
  EXPECT_EQ(r.value, Val4::kX);
  // Figure 28-15 draws the range from St0 up to St1, so strong is the high end
  // on both sides and high impedance the low end on both sides.
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength0_lo, StrengthLevel::kHighz);
  EXPECT_EQ(r.strength1_lo, StrengthLevel::kHighz);
}

// Two components on one side of the scale: a pull H and the strong H of
// Figure 28-7 combine into the strong H range. "The combination of two signals
// of ambiguous strength shall result in a signal of ambiguous strength. The
// resulting signal shall have a range of strength levels that includes the
// strength levels in its component signals." Both components run from high
// impedance, the pull H up to Pu1 and the strong H up to St1, so the range
// holding the levels of both is HiZ1 through St1 and no strength0 level joins
// it.
//
// The `value` field is not asserted. §28.12.2 classifies this result as a
// signal with a value H, and Val4 in lib/cpp/test_models/model_val4.h has no H
// among kV0, kV1, kX and kZ, so the clause decides nothing about what
// CombineAmbiguous should put there.
TEST(AmbiguousStrengthModelCombine, PullHAndStrongHGiveStrongHRange) {
  StrengthSignal pull_h =
      Strength1Range(StrengthLevel::kHighz, StrengthLevel::kPull);
  StrengthSignal strong_h =
      Strength1Range(StrengthLevel::kHighz, StrengthLevel::kStrong);

  StrengthSignal r = CombineAmbiguous(pull_h, strong_h);

  EXPECT_EQ(r.strength1_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength1_lo, StrengthLevel::kHighz);
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kHighz);
  EXPECT_EQ(r.strength0_lo, StrengthLevel::kHighz);
}

// Two components of the same value, neither of which reaches high impedance: a
// value-1 signal spanning Pu1 through St1 combines with a value-1 signal
// spanning We1 through La1 into a value-1 signal spanning We1 through St1.
// "The combination of two signals of ambiguous strength shall result in a
// signal of ambiguous strength. The resulting signal shall have a range of
// strength levels that includes the strength levels in its component signals",
// which Figure 28-9 draws as "a range that includes the extremes of the signals
// and all the strengths between them". We1 is the lower extreme of the two
// components and St1 the upper, so the range runs from one to the other and no
// further.
//
// This is the case issue #3423 records. Before that issue CombineAmbiguous read
// the strength0_hi and strength1_hi fields alone, so it answered this
// combination a strength1_lo of high impedance, which is a range down to HiZ1
// holding six levels that neither component holds.
//
// The value is asserted here and not in PullHAndStrongHGiveStrongHRange above,
// because a range clear of HiZ1 is one §28.12.2 gives a defined value. Of
// Figure 28-12's Pu1 through St1 range the clause says the upper configuration
// of Figure 28-11 "produces a signal with a value of 1 and a range of strengths
// (651)".
TEST(AmbiguousStrengthModelCombine,
     ValueOneRangesClearOfHighzKeepTheirExtreme) {
  StrengthSignal pull_to_strong_one =
      Strength1Range(StrengthLevel::kPull, StrengthLevel::kStrong);
  StrengthSignal weak_to_large_one =
      Strength1Range(StrengthLevel::kWeak, StrengthLevel::kLarge);

  StrengthSignal r = CombineAmbiguous(pull_to_strong_one, weak_to_large_one);

  EXPECT_EQ(r.value, Val4::kV1);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength1_lo, StrengthLevel::kWeak);
  // No strength0 level lies between We1 and St1, so none of them is in the
  // result.
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kHighz);
  EXPECT_EQ(r.strength0_lo, StrengthLevel::kHighz);
}

}  // namespace
