#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_net_strength.h"
#include "model_strength.h"
#include "model_val4.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

struct Width1Driver {
  uint64_t value;
  Strength strength;
};

StrengthNet ResolveWidth1(Arena& arena,
                          std::initializer_list<Width1Driver> drivers) {
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;
  for (const Width1Driver& d : drivers) {
    AddDriver(arena, net, 1, d.value, d.strength);
  }
  net.Resolve(arena);
  return sn;
}

void ExpectResolvedStrengthsAndX(const StrengthNet& sn, Strength s0_hi,
                                 Strength s0_lo, Strength s1_hi,
                                 Strength s1_lo) {
  const Net& net = sn.net;
  EXPECT_EQ(net.resolved_strength.s0_hi, s0_hi);
  EXPECT_EQ(net.resolved_strength.s0_lo, s0_lo);
  EXPECT_EQ(net.resolved_strength.s1_hi, s1_hi);
  EXPECT_EQ(net.resolved_strength.s1_lo, s1_lo);
  EXPECT_EQ(sn.var->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(sn.var->value.words[0].bval & 1u, 1u);
}

std::string ConflictPlusWeakerSrc(const std::string& weaker) {
  return "module m;\n"
         "  wire w;\n"
         "  assign (strong0, strong1) w = 1'b0;\n"
         "  assign (strong0, strong1) w = 1'b1;\n" +
         weaker + "endmodule\n";
}

NetStrength ResolveSrcNetW(const std::string& src) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (design == nullptr) return {};
  LowerAndRun(design, f);
  const Net* net = f.ctx.FindNet("w");
  EXPECT_NE(net, nullptr);
  return net == nullptr ? NetStrength{} : net->resolved_strength;
}

StrengthSignal UnambiguousSignal(Val4 value, StrengthLevel level) {
  StrengthSignal signal;
  signal.value = value;
  if (value == Val4::kV0) {
    signal.strength0_hi = level;
    signal.strength0_lo = level;
  } else {
    signal.strength1_hi = level;
    signal.strength1_lo = level;
  }
  return signal;
}

StrengthSignal AmbiguousRange(Val4 value, StrengthLevel lo, StrengthLevel hi) {
  bool on_side_0 = value == Val4::kV0 || value == Val4::kX;
  bool on_side_1 = value == Val4::kV1 || value == Val4::kX;
  StrengthSignal signal;
  signal.value = value;
  if (on_side_0) {
    signal.strength0_hi = hi;
    signal.strength0_lo = lo;
  }
  if (on_side_1) {
    signal.strength1_hi = hi;
    signal.strength1_lo = lo;
  }
  return signal;
}

TEST(StrengthCombineAmbigUnambig, RuleAPreservesHighEndOfRange) {
  StrengthSignal unambig = UnambiguousSignal(Val4::kV0, StrengthLevel::kSmall);
  StrengthSignal ambig =
      AmbiguousRange(Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kWeak);
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kSmall);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kWeak);
}

TEST(StrengthCombineAmbigUnambig, RuleATrimsLowEndButKeepsHigh) {
  StrengthSignal unambig = UnambiguousSignal(Val4::kV0, StrengthLevel::kPull);
  StrengthSignal ambig =
      AmbiguousRange(Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kStrong);
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kHighz);
}

TEST(StrengthCombineAmbigUnambig, RuleBEliminatesAmbigAtOrBelowSu) {
  StrengthSignal unambig = UnambiguousSignal(Val4::kV0, StrengthLevel::kStrong);
  StrengthSignal ambig =
      AmbiguousRange(Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kWeak);
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kV0);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kHighz);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kHighz);
}

TEST(StrengthCombineAmbigUnambig, RuleBEliminatesAmbigAtExactlySu) {
  StrengthSignal unambig = UnambiguousSignal(Val4::kV0, StrengthLevel::kPull);
  StrengthSignal ambig =
      AmbiguousRange(Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kPull);
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kV0);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kHighz);
}

TEST(StrengthCombineAmbigUnambig, RuleBSameValueMergeWithUnambig) {
  StrengthSignal unambig = UnambiguousSignal(Val4::kV0, StrengthLevel::kWeak);
  StrengthSignal ambig =
      AmbiguousRange(Val4::kV0, StrengthLevel::kHighz, StrengthLevel::kStrong);
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kV0);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kWeak);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kHighz);
}

TEST(StrengthCombineAmbigUnambig, RuleCFillsGapOnOppositeSide) {
  StrengthSignal unambig = UnambiguousSignal(Val4::kV0, StrengthLevel::kPull);
  StrengthSignal ambig =
      AmbiguousRange(Val4::kV1, StrengthLevel::kSupply, StrengthLevel::kSupply);
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kSupply);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kHighz);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kPull);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kHighz);
}

TEST(StrengthCombineAmbigUnambig, RuleCFillsMultiLevelGap) {
  StrengthSignal unambig = UnambiguousSignal(Val4::kV0, StrengthLevel::kWeak);
  StrengthSignal ambig =
      AmbiguousRange(Val4::kV1, StrengthLevel::kStrong, StrengthLevel::kSupply);
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kSupply);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kHighz);
}

TEST(StrengthCombineAmbigUnambig, RuleCDoesNotFillSameSideGap) {
  StrengthSignal unambig = UnambiguousSignal(Val4::kV0, StrengthLevel::kWeak);
  StrengthSignal ambig =
      AmbiguousRange(Val4::kV0, StrengthLevel::kStrong, StrengthLevel::kSupply);
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kV0);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kSupply);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kHighz);
}

TEST(StrengthCombineAmbigUnambig, RulesAAndBApplyPerSide) {
  StrengthSignal unambig = UnambiguousSignal(Val4::kV0, StrengthLevel::kPull);
  StrengthSignal ambig =
      AmbiguousRange(Val4::kX, StrengthLevel::kHighz, StrengthLevel::kStrong);
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kHighz);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kHighz);
}

TEST(StrengthCombineAmbigUnambig, SupplyUnambigWipesAllAmbig) {
  StrengthSignal unambig = UnambiguousSignal(Val4::kV0, StrengthLevel::kSupply);
  StrengthSignal ambig =
      AmbiguousRange(Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kSupply);
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kV0);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kSupply);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kHighz);
}

TEST(StrengthCombineAmbigUnambig, MirrorWithV1Unambig) {
  StrengthSignal unambig = UnambiguousSignal(Val4::kV1, StrengthLevel::kPull);
  StrengthSignal ambig =
      AmbiguousRange(Val4::kV0, StrengthLevel::kHighz, StrengthLevel::kStrong);
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kPull);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kHighz);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kHighz);
}

TEST(StrengthCombineAmbigUnambig, RuleCFillsGapOnOppositeSideMirror) {
  StrengthSignal unambig = UnambiguousSignal(Val4::kV1, StrengthLevel::kPull);
  StrengthSignal ambig =
      AmbiguousRange(Val4::kV0, StrengthLevel::kSupply, StrengthLevel::kSupply);
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kSupply);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kHighz);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kPull);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kHighz);
}

TEST(StrengthCombineAmbigUnambig, HighZUnambigPreservesEntireAmbig) {
  StrengthSignal unambig = UnambiguousSignal(Val4::kV0, StrengthLevel::kHighz);
  StrengthSignal ambig =
      AmbiguousRange(Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kPull);
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kPull);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kHighz);
}

TEST(StrengthResolution, RuleAAndBTrimAmbigLoBoundsPerSide) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(
      arena,
      {{0, Strength::kPull}, {1, Strength::kPull}, {0, Strength::kWeak}});

  ExpectResolvedStrengthsAndX(sn, Strength::kPull, Strength::kHighz,
                              Strength::kPull, Strength::kHighz);
}

TEST(StrengthResolution, RuleAAndBTrimAmbigLoBoundsPerSideVuOne) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(
      arena,
      {{0, Strength::kStrong}, {1, Strength::kStrong}, {1, Strength::kWeak}});

  ExpectResolvedStrengthsAndX(sn, Strength::kStrong, Strength::kHighz,
                              Strength::kStrong, Strength::kHighz);
  EXPECT_TRUE(sn.net.resolved_strength.IsAmbiguous());
}

TEST(StrengthResolution, RuleBAtAmbigHiMinusOnePerSide) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(
      arena,
      {{0, Strength::kStrong}, {1, Strength::kStrong}, {0, Strength::kPull}});

  ExpectResolvedStrengthsAndX(sn, Strength::kStrong, Strength::kHighz,
                              Strength::kStrong, Strength::kHighz);
  EXPECT_TRUE(sn.net.resolved_strength.IsAmbiguous());
}

TEST(StrengthResolution, AmbigUnambigPerBitIndependence) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 4);
  Net& net = sn.net;

  AddDriver(arena, net, 4, 0b1100, Strength::kPull);
  AddDriver(arena, net, 4, 0b0011, Strength::kPull);
  AddDriver(arena, net, 4, 0b1010, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(sn.var->value.ToUint64() & 0xFu, 0b1010u);
}

TEST(StrengthResolution, RuleBCompleteEliminationProducesUnambigResult) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(
      arena,
      {{0, Strength::kPull}, {1, Strength::kPull}, {0, Strength::kStrong}});
  Net& net = sn.net;

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kHighz);
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
  EXPECT_EQ(sn.var->value.ToUint64(), 0u);
}

TEST(StrengthResolution, SecondWeakerDriverBelowTheFirstWidensNothing) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(arena, {{0, Strength::kStrong},
                                         {1, Strength::kStrong},
                                         {0, Strength::kPull},
                                         {0, Strength::kWeak}});

  ExpectResolvedStrengthsAndX(sn, Strength::kStrong, Strength::kHighz,
                              Strength::kStrong, Strength::kHighz);
}

TEST(StrengthResolution, OppositeValueWeakerDriversAtOneLevelBothCombine) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(arena, {{0, Strength::kStrong},
                                         {1, Strength::kStrong},
                                         {0, Strength::kPull},
                                         {1, Strength::kPull}});

  ExpectResolvedStrengthsAndX(sn, Strength::kStrong, Strength::kHighz,
                              Strength::kStrong, Strength::kHighz);
  EXPECT_TRUE(sn.net.resolved_strength.IsAmbiguous());
}

TEST(StrengthResolution, SameValueWeakerDriversAtOneLevelCombineIdempotently) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(arena, {{0, Strength::kStrong},
                                         {1, Strength::kStrong},
                                         {0, Strength::kPull},
                                         {0, Strength::kPull}});

  ExpectResolvedStrengthsAndX(sn, Strength::kStrong, Strength::kHighz,
                              Strength::kStrong, Strength::kHighz);
}

TEST(StrengthResolution, HighzWeakerDriverLeavesTheConflictRangeWhole) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(
      arena,
      {{0, Strength::kStrong}, {1, Strength::kStrong}, {0, Strength::kHighz}});

  ExpectResolvedStrengthsAndX(sn, Strength::kStrong, Strength::kHighz,
                              Strength::kStrong, Strength::kHighz);
}

TEST(StrengthResolution, RuleAAndBAtSmallestNonHighzSu) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(
      arena,
      {{0, Strength::kPull}, {1, Strength::kPull}, {0, Strength::kSmall}});

  ExpectResolvedStrengthsAndX(sn, Strength::kPull, Strength::kHighz,
                              Strength::kPull, Strength::kHighz);
}

TEST(StrengthResolution, RuleAKeepsSupplyLevelAtTopOfScale) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(
      arena,
      {{0, Strength::kSupply}, {1, Strength::kSupply}, {0, Strength::kStrong}});

  ExpectResolvedStrengthsAndX(sn, Strength::kSupply, Strength::kHighz,
                              Strength::kSupply, Strength::kHighz);
  EXPECT_TRUE(sn.net.resolved_strength.IsAmbiguous());
}

TEST(StrengthResolution, RuleBCompleteEliminationYieldsUnambigOne) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(
      arena,
      {{0, Strength::kPull}, {1, Strength::kPull}, {1, Strength::kStrong}});
  Net& net = sn.net;

  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kHighz);
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
  EXPECT_EQ(sn.var->value.ToUint64(), 1u);
}

TEST(NetStrengthAmbigUnambig, RuleCFillsTheGapOnTheOppositeValueSide) {
  NetStrength ambig;
  ambig.s1_hi = Strength::kSupply;
  ambig.s1_lo = Strength::kSupply;
  NetStrength r = CombineAmbigWithUnambig(ambig, 0, 5);
  EXPECT_EQ(r.s1_hi, Strength::kSupply);
  EXPECT_EQ(r.s1_lo, Strength::kHighz);
  EXPECT_EQ(r.s0_hi, Strength::kPull);
  EXPECT_EQ(r.s0_lo, Strength::kHighz);
}

TEST(NetStrengthAmbigUnambig, RuleCFillsAGapOfSeveralLevels) {
  NetStrength ambig;
  ambig.s1_hi = Strength::kSupply;
  ambig.s1_lo = Strength::kStrong;
  NetStrength r = CombineAmbigWithUnambig(ambig, 0, 3);
  EXPECT_EQ(r.s1_hi, Strength::kSupply);
  EXPECT_EQ(r.s1_lo, Strength::kHighz);
}

TEST(NetStrengthAmbigUnambig, SameValueRangeAboveTheUnambiguousLevelKeepsIt) {
  NetStrength ambig;
  ambig.s0_hi = Strength::kSupply;
  ambig.s0_lo = Strength::kStrong;
  NetStrength r = CombineAmbigWithUnambig(ambig, 0, 3);
  EXPECT_EQ(r.s0_hi, Strength::kSupply);
  EXPECT_EQ(r.s0_lo, Strength::kStrong);
  EXPECT_EQ(r.s1_hi, Strength::kHighz);
}

TEST(NetStrengthAmbigUnambig, SameValueRangeStraddlingTheUnambiguousLevel) {
  NetStrength ambig;
  ambig.s0_hi = Strength::kSupply;
  ambig.s0_lo = Strength::kSmall;
  NetStrength r = CombineAmbigWithUnambig(ambig, 0, 3);
  EXPECT_EQ(r.s0_hi, Strength::kSupply);
  EXPECT_EQ(r.s0_lo, Strength::kWeak);
}

TEST(NetStrengthAmbigUnambig, OppositeValueRangeAtOrBelowSuDisappears) {
  NetStrength ambig;
  ambig.s1_hi = Strength::kWeak;
  ambig.s1_lo = Strength::kSmall;
  NetStrength r = CombineAmbigWithUnambig(ambig, 0, 6);
  EXPECT_EQ(r.s1_hi, Strength::kHighz);
  EXPECT_EQ(r.s1_lo, Strength::kHighz);
  EXPECT_EQ(r.s0_hi, Strength::kStrong);
  EXPECT_EQ(r.s0_lo, Strength::kStrong);
}

TEST(NetStrengthAmbigUnambig, RulesFollowTheValueAndNotTheSide) {
  NetStrength ambig;
  ambig.s0_hi = Strength::kSupply;
  ambig.s0_lo = Strength::kSupply;
  NetStrength r = CombineAmbigWithUnambig(ambig, 1, 5);
  EXPECT_EQ(r.s0_hi, Strength::kSupply);
  EXPECT_EQ(r.s0_lo, Strength::kHighz);
  EXPECT_EQ(r.s1_hi, Strength::kPull);
  EXPECT_EQ(r.s1_lo, Strength::kHighz);
}

TEST(NetStrengthAmbigUnambig, DominatingAmbiguousSignalKeepsItsOwnRange) {
  NetStrength ambig;
  ambig.s0_hi = Strength::kStrong;
  ambig.s0_lo = Strength::kPull;
  ambig.s1_hi = Strength::kStrong;
  ambig.s1_lo = Strength::kStrong;
  NetStrength r = CombineAmbigWithUnambig(ambig, 1, 3);
  EXPECT_EQ(r.s0_hi, Strength::kStrong);
  EXPECT_EQ(r.s0_lo, Strength::kHighz);
  EXPECT_EQ(r.s1_hi, Strength::kStrong);
  EXPECT_EQ(r.s1_lo, Strength::kHighz);
}

TEST(StrengthResolution, SourceOppositeValuePullDriversRenderAsStX) {
  NetStrength ns = ResolveSrcNetW(
      ConflictPlusWeakerSrc("  assign (pull0, pull1) w = 1'b0;\n"
                            "  assign (pull0, pull1) w = 1'b1;\n"));
  EXPECT_EQ(ns.s0_hi, Strength::kStrong);
  EXPECT_EQ(ns.s0_lo, Strength::kHighz);
  EXPECT_EQ(ns.s1_hi, Strength::kStrong);
  EXPECT_EQ(ns.s1_lo, Strength::kHighz);
  EXPECT_EQ(FormatStrength(ns), "StX");
}

TEST(StrengthResolution, SourceHighzStrengthDriverLeavesTheConflictRangeWhole) {
  NetStrength ns = ResolveSrcNetW(
      ConflictPlusWeakerSrc("  assign (highz0, strong1) w = 1'b0;\n"));
  EXPECT_EQ(ns.s0_hi, Strength::kStrong);
  EXPECT_EQ(ns.s0_lo, Strength::kHighz);
  EXPECT_EQ(ns.s1_hi, Strength::kStrong);
  EXPECT_EQ(ns.s1_lo, Strength::kHighz);
}

TEST(NetStrengthAmbigUnambig, OppositeValueGapFillsAcrossHighImpedance) {
  NetStrength ambig;
  ambig.s1_hi = Strength::kStrong;
  ambig.s1_lo = Strength::kHighz;
  NetStrength r = CombineAmbigWithUnambig(ambig, 0, 5);
  EXPECT_EQ(r.s0_hi, Strength::kPull);
  EXPECT_EQ(r.s0_lo, Strength::kHighz);
  EXPECT_EQ(r.s1_hi, Strength::kStrong);
  EXPECT_EQ(r.s1_lo, Strength::kHighz);
}

TEST(NetStrengthAmbigUnambig, SameSideRangeStopsAtTheUnambiguousLevel) {
  NetStrength ambig;
  ambig.s1_hi = Strength::kPull;
  ambig.s1_lo = Strength::kHighz;
  NetStrength r = CombineAmbigWithUnambig(ambig, 1, 2);
  EXPECT_EQ(r.s1_hi, Strength::kPull);
  EXPECT_EQ(r.s1_lo, Strength::kMedium);
  EXPECT_EQ(r.s0_hi, Strength::kHighz);
  EXPECT_EQ(r.s0_lo, Strength::kHighz);
}

TEST(NetStrengthAmbigUnambig, LevelsAtOrBelowTheUnambiguousLevelAreEliminated) {
  NetStrength ambig;
  ambig.s0_hi = Strength::kStrong;
  ambig.s0_lo = Strength::kHighz;
  NetStrength r = CombineAmbigWithUnambig(ambig, 0, 5);
  EXPECT_EQ(r.s0_hi, Strength::kStrong);
  EXPECT_EQ(r.s0_lo, Strength::kPull);
  EXPECT_EQ(r.s1_hi, Strength::kHighz);
}

TEST(NetStrengthAmbigUnambig,
     WeakOppositeSideLeavesTheRangeFromSuToTheExtreme) {
  NetStrength ambig;
  ambig.s0_hi = Strength::kWeak;
  ambig.s0_lo = Strength::kHighz;
  ambig.s1_hi = Strength::kStrong;
  ambig.s1_lo = Strength::kHighz;
  NetStrength r = CombineAmbigWithUnambig(ambig, 1, 5);
  EXPECT_EQ(r.s1_hi, Strength::kStrong);
  EXPECT_EQ(r.s1_lo, Strength::kPull);
  EXPECT_EQ(r.s0_hi, Strength::kHighz);
  EXPECT_EQ(r.s0_lo, Strength::kHighz);
}

struct ExpectedBounds {
  StrengthLevel s0_hi;
  StrengthLevel s0_lo;
  StrengthLevel s1_hi;
  StrengthLevel s1_lo;
};

void ExpectModelAndCombinerAgree(StrengthSignal ambig, Val4 vu,
                                 StrengthLevel su, const ExpectedBounds& want) {
  StrengthSignal modelled =
      CombineAmbiguousWithUnambiguous(UnambiguousSignal(vu, su), ambig);
  EXPECT_EQ(modelled.strength0_hi, want.s0_hi);
  EXPECT_EQ(modelled.strength0_lo, want.s0_lo);
  EXPECT_EQ(modelled.strength1_hi, want.s1_hi);
  EXPECT_EQ(modelled.strength1_lo, want.s1_lo);

  NetStrength ns;
  ns.s0_hi = static_cast<Strength>(ambig.strength0_hi);
  ns.s0_lo = static_cast<Strength>(ambig.strength0_lo);
  ns.s1_hi = static_cast<Strength>(ambig.strength1_hi);
  ns.s1_lo = static_cast<Strength>(ambig.strength1_lo);
  NetStrength r = CombineAmbigWithUnambig(ns, vu == Val4::kV0 ? 0 : 1,
                                          static_cast<uint8_t>(su));
  EXPECT_EQ(r.s0_hi, static_cast<Strength>(want.s0_hi));
  EXPECT_EQ(r.s0_lo, static_cast<Strength>(want.s0_lo));
  EXPECT_EQ(r.s1_hi, static_cast<Strength>(want.s1_hi));
  EXPECT_EQ(r.s1_lo, static_cast<Strength>(want.s1_lo));
}

TEST(NetStrengthAmbigUnambig, ModelAndCombinerAgreeOnAGapAcrossHighImpedance) {
  ExpectModelAndCombinerAgree(
      AmbiguousRange(Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kStrong),
      Val4::kV0, StrengthLevel::kPull,
      {StrengthLevel::kPull, StrengthLevel::kHighz, StrengthLevel::kStrong,
       StrengthLevel::kHighz});
}

TEST(NetStrengthAmbigUnambig, ModelAndCombinerAgreeOnAResolverConflictRange) {
  ExpectModelAndCombinerAgree(
      AmbiguousRange(Val4::kX, StrengthLevel::kHighz, StrengthLevel::kStrong),
      Val4::kV0, StrengthLevel::kPull,
      {StrengthLevel::kStrong, StrengthLevel::kHighz, StrengthLevel::kStrong,
       StrengthLevel::kHighz});
}

TEST(NetStrengthAmbigUnambig, ModelAndCombinerAgreeWithNoOppositeSurvivor) {
  ExpectModelAndCombinerAgree(
      AmbiguousRange(Val4::kV0, StrengthLevel::kHighz, StrengthLevel::kStrong),
      Val4::kV0, StrengthLevel::kPull,
      {StrengthLevel::kStrong, StrengthLevel::kPull, StrengthLevel::kHighz,
       StrengthLevel::kHighz});
}

}  // namespace
