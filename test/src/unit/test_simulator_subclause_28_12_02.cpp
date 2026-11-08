#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_net_strength.h"
#include "model_strength.h"
#include "model_val4.h"
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

  EXPECT_EQ(sn.var->value.words[0].aval & 0xFFu, 0xFFu);
  EXPECT_EQ(sn.var->value.words[0].bval & 0xFFu, 0xFFu);
}

TEST(StrengthResolution, EqualStrengthPartialConflictPerBit) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 4);
  Net& net = sn.net;

  AddDriver(arena, net, 4, 0b1100, Strength::kStrong);
  AddDriver(arena, net, 4, 0b1010, Strength::kStrong);
  net.Resolve(arena);

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

  EXPECT_EQ(sn.var->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(sn.var->value.words[0].bval & 1u, 1u);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_TRUE(net.resolved_strength.IsAmbiguous());
}

TEST(AmbiguousStrengthClass, KnownValueMultiLevelIsAmbiguous) {
  NetStrength ns;
  ns.s1_hi = Strength::kStrong;
  ns.s1_lo = Strength::kWeak;
  EXPECT_TRUE(ns.IsAmbiguous());
  EXPECT_EQ(ns.s0_hi, Strength::kHighz);
  EXPECT_EQ(ns.s0_lo, Strength::kHighz);
}

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

TEST(AmbiguousStrengthClass, LValueIsHighZJoinedWithStrengthZeroRange) {
  NetStrength ns;
  ns.s0_hi = Strength::kStrong;
  ns.s0_lo = Strength::kHighz;
  EXPECT_TRUE(ns.IsAmbiguous());
  EXPECT_EQ(ns.s1_hi, Strength::kHighz);
  EXPECT_EQ(ns.s1_lo, Strength::kHighz);
}

TEST(AmbiguousStrengthClass, HValueIsHighZJoinedWithStrengthOneRange) {
  NetStrength ns;
  ns.s1_hi = Strength::kStrong;
  ns.s1_lo = Strength::kHighz;
  EXPECT_TRUE(ns.IsAmbiguous());
  EXPECT_EQ(ns.s0_hi, Strength::kHighz);
  EXPECT_EQ(ns.s0_lo, Strength::kHighz);
}

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

static Net* RunAndFindNetW(SimFixture& f, const char* src) {
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return nullptr;
  LowerAndRun(design, f);
  return f.ctx.FindNet("w");
}

static void ExpectXSpanningDownToHighz(SimFixture& f, Net* net, Strength hi) {
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
  EXPECT_EQ(net->resolved_strength.s0_hi, hi);
  EXPECT_EQ(net->resolved_strength.s1_hi, hi);
  EXPECT_EQ(net->resolved_strength.s0_lo, Strength::kHighz);
  EXPECT_EQ(net->resolved_strength.s1_lo, Strength::kHighz);
  EXPECT_TRUE(net->resolved_strength.IsAmbiguous());
}

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

TEST(StrengthResolutionPipeline, EqualStrengthConflictFromGateOutputs) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wire w;\n"
                            "  wire a = 1'b1, b = 1'b1;\n"
                            "  wire c = 1'b0, d = 1'b1;\n"
                            "  and (weak0, weak1) g0(w, a, b);\n"
                            "  and (weak0, weak1) g1(w, c, d);\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
  EXPECT_EQ(net->resolved_strength.s0_hi, Strength::kWeak);
  EXPECT_EQ(net->resolved_strength.s1_hi, Strength::kWeak);
  EXPECT_TRUE(net->resolved_strength.IsAmbiguous());
}

TEST(StrengthResolutionPipeline, EqualStrengthConflictFromNetDeclInitializer) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wire (strong0, strong1) w = 1'b1;\n"
                            "  assign (strong0, strong1) w = 1'b0;\n"
                            "endmodule\n");
  ExpectXSpanningDownToHighz(f, net, Strength::kStrong);
}

TEST(StrengthResolutionPipeline, EqualStrengthConflictVectorResolvesPerBit) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wire [3:0] w;\n"
                            "  wire [3:0] p = 4'b1100, q = 4'b1010;\n"
                            "  buf (strong0, strong1) g[3:0] (w, p);\n"
                            "  buf (strong0, strong1) h[3:0] (w, q);\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0xFu, 0b1110u);
  EXPECT_EQ(var->value.words[0].bval & 0xFu, 0b0110u);
}

StrengthSignal Strength0Range(StrengthLevel lo, StrengthLevel hi) {
  StrengthSignal s;
  s.value = Val4::kV0;
  s.strength0_lo = lo;
  s.strength0_hi = hi;
  return s;
}

StrengthSignal Strength1Range(StrengthLevel lo, StrengthLevel hi) {
  StrengthSignal s;
  s.value = Val4::kV1;
  s.strength1_lo = lo;
  s.strength1_hi = hi;
  return s;
}

TEST(AmbiguousStrengthModelCombine, PullHAndWeakLGiveThreeFiveX) {
  StrengthSignal pull_h =
      Strength1Range(StrengthLevel::kHighz, StrengthLevel::kPull);
  StrengthSignal weak_l =
      Strength0Range(StrengthLevel::kHighz, StrengthLevel::kWeak);

  StrengthSignal r = CombineAmbiguous(pull_h, weak_l);

  EXPECT_EQ(r.value, Val4::kX);
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kWeak);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kPull);
  EXPECT_EQ(r.strength0_lo, StrengthLevel::kHighz);
  EXPECT_EQ(r.strength1_lo, StrengthLevel::kHighz);
}

TEST(AmbiguousStrengthModelCombine, SwitchNetworkRangesGiveFiveSixX) {
  StrengthSignal upper =
      Strength1Range(StrengthLevel::kPull, StrengthLevel::kStrong);
  StrengthSignal lower =
      Strength0Range(StrengthLevel::kWeak, StrengthLevel::kPull);

  StrengthSignal r = CombineAmbiguous(upper, lower);

  EXPECT_EQ(r.value, Val4::kX);
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kPull);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength0_lo, StrengthLevel::kHighz);
  EXPECT_EQ(r.strength1_lo, StrengthLevel::kHighz);
}

TEST(AmbiguousStrengthModelCombine, StrongExtremesGiveStrongX) {
  StrengthSignal upper =
      Strength1Range(StrengthLevel::kPull, StrengthLevel::kStrong);
  StrengthSignal lower =
      Strength0Range(StrengthLevel::kWeak, StrengthLevel::kStrong);

  StrengthSignal r = CombineAmbiguous(upper, lower);

  EXPECT_EQ(r.value, Val4::kX);
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength0_lo, StrengthLevel::kHighz);
  EXPECT_EQ(r.strength1_lo, StrengthLevel::kHighz);
}

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
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kHighz);
  EXPECT_EQ(r.strength0_lo, StrengthLevel::kHighz);
}

std::string ResolvedStrengthOf(const std::string& body) {
  SimFixture f;
  return RunCapture("module t;\n  wire y;\n" + body +
                        "  initial #1 $display(\"%v\", y);\nendmodule\n",
                    f);
}

TEST(StrengthResolution, SourceTwoAmbiguousGatesCombineIntoOneAmbiguousRange) {
  EXPECT_EQ(ResolvedStrengthOf(
                "  logic d1, d0, c;\n"
                "  bufif1 (pull0, pull1) g1 (y, d1, c);\n"
                "  bufif1 (weak0, weak1) g0 (y, d0, c);\n"
                "  initial begin d1 = 1'b1; d0 = 1'b0; c = 1'bx; end\n"),
            "35X\n");
}

TEST(StrengthResolution, SourceUnknownValueDriverGivesItsOwnStrength) {
  EXPECT_EQ(ResolvedStrengthOf("  assign (pull0, pull1) y = 1'bx;\n"), "PuX\n");
}

TEST(StrengthResolution, SourceStrongHBesideAPullupIs651) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire u;\n"
      "  logic a = 1, b = 1'bx;\n"
      "  pmos p (u, a, b);\n"
      "  pullup (u);\n"
      "  initial #1 $display(\"u=%b %v\", u, u);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "u=1 651\n");
}

TEST(StrengthResolution, SourcePullLBesideAWeakZeroIs530) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire l, pd;\n"
      "  logic g = 1'bx, d = 0;\n"
      "  pulldown (pd);\n"
      "  pmos p (l, pd, g);\n"
      "  and (strong1, weak0) a (l, d, d);\n"
      "  initial #1 $display(\"l=%b %v\", l, l);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "l=0 530\n");
}

TEST(StrengthResolution, SourceHAndLCombinationsOnOneNetAre56X) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire y, pd;\n"
      "  logic a = 1, b = 1'bx, g = 1'bx, d = 0;\n"
      "  pmos p1 (y, a, b);\n"
      "  pullup (y);\n"
      "  pulldown (pd);\n"
      "  pmos p2 (y, pd, g);\n"
      "  and (strong1, weak0) an (y, d, d);\n"
      "  initial #1 $display(\"y=%b %v\", y, y);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "y=x 56X\n");
}

TEST(StrengthResolution, SourceStrongHWithWeakZeroIs36X) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire y, w;\n"
      "  logic a = 1, b = 1'bx, zero = 0;\n"
      "  and (strong1, highz0) n1 (y, a, b);\n"
      "  and (strong1, weak0) n2 (y, zero, zero);\n"
      "  pmos p (w, a, b);\n"
      "  pullup (w);\n"
      "  and (strong1, weak0) n3 (w, zero, zero);\n"
      "  initial #1 $display(\"y=%b %v w=%b %v\", y, y, w, w);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "y=x 36X w=1 651\n");
}

}  // namespace
