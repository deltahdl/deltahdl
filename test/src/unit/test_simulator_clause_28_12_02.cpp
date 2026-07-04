#include <gtest/gtest.h>

#include "common/arena.h"
#include "fixture_simulator.h"
#include "helpers_net_strength.h"
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
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 1u, 1u);  // x = (aval=1, bval=1)
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
  EXPECT_EQ(net->resolved_strength.s0_hi, Strength::kWeak);
  EXPECT_EQ(net->resolved_strength.s1_hi, Strength::kWeak);
  EXPECT_EQ(net->resolved_strength.s0_lo, Strength::kHighz);
  EXPECT_EQ(net->resolved_strength.s1_lo, Strength::kHighz);
  EXPECT_TRUE(net->resolved_strength.IsAmbiguous());
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
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
  EXPECT_EQ(net->resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net->resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(net->resolved_strength.s0_lo, Strength::kHighz);
  EXPECT_EQ(net->resolved_strength.s1_lo, Strength::kHighz);
  EXPECT_TRUE(net->resolved_strength.IsAmbiguous());
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
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 1u, 1u);  // x
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
  EXPECT_EQ(net->resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net->resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(net->resolved_strength.s0_lo, Strength::kHighz);
  EXPECT_EQ(net->resolved_strength.s1_lo, Strength::kHighz);
  EXPECT_TRUE(net->resolved_strength.IsAmbiguous());
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

}  // namespace
