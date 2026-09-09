// §28.12.3: combining a signal of known value and unambiguous strength with a
// signal of ambiguous strength, under that subclause's rules a), b) and c).
//
// Every StrengthSignal operand below is written in the encoding StrengthSignal
// states in lib/cpp/test_models/model_strength.h, where a side is occupied when
// its _hi is above kHighz and then occupies every level from its _lo up to that
// _hi. UnambiguousSignal and AmbiguousRange below build the two kinds of
// operand, so each case names the kind it means rather than listing four
// fields.

#include <gtest/gtest.h>

#include <initializer_list>
#include <string>

#include "common/arena.h"
#include "fixture_simulator.h"
#include "helpers_net_strength.h"
#include "model_strength.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// One (value, strength) pair for a width-1 net driver.
struct Width1Driver {
  uint64_t value;
  Strength strength;
};

// Builds a width-1 strength net, appends each given width-1 driver in order,
// resolves the net, and returns the StrengthNet so the caller can assert on the
// resolved strengths and backing variable. Centralizes the
// Arena/MakeStrengthNet/AddDriver/Resolve setup shared by the width-1
// StrengthResolution tests.
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

// Asserts the four resolved strength bounds of a width-1 net and that bit 0 of
// its backing variable holds an x. Canonical Convention A encodes x as
// (aval=1, bval=1). Centralizes the six-line assertion block shared by the
// ambiguous-result StrengthResolution tests.
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

// A module driving the scalar net w from the two equally strong drivers of
// opposite value §28.12.2 makes an ambiguous signal out of, followed by the
// weaker continuous assignments `weaker` supplies.
std::string ConflictPlusWeakerSrc(const std::string& weaker) {
  return "module m;\n"
         "  wire w;\n"
         "  assign (strong0, strong1) w = 1'b0;\n"
         "  assign (strong0, strong1) w = 1'b1;\n" +
         weaker + "endmodule\n";
}

// Elaborates, lowers and runs `src`, then returns the resolved strength of the
// scalar net w it declares. Centralizes the elaborate/lower/run and net lookup
// shared by the StrengthResolution tests that drive a net from real source
// rather than by appending drivers to a Net directly.
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

// The signal of known value and unambiguous strength §28.12.3 combines an
// ambiguous signal with, driving `value` at the single level `level`. Such a
// signal occupies one cell of Figure 28-2's scale, so StrengthSignal in
// lib/cpp/test_models/model_strength.h writes it with _lo equal to _hi on the
// side its value stands on. §28.12.3's unambiguous signal has a known value, so
// `value` is Val4::kV0 or Val4::kV1.
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

// A signal of ambiguous strength occupying every level from `lo` up to `hi`.
// The value names the side the range stands on: Val4::kV0 the strength0 side,
// Val4::kV1 the strength1 side, and Val4::kX both sides, which is the signal
// §28.12.2 makes out of two equally strong drivers of opposite value. A range
// left at StrengthLevel::kHighz on its low end reaches high impedance, which is
// what §28.12.3's rules a) and b) trim.
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
  // Rule c: the strong 1 survives the pull 0, and the gap between the two
  // crosses high impedance, so the side reaches it (Figure 28-23).
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

// §28.12.3 makes one combination per signal of known value and unambiguous
// strength, so the weak 0 here is combined as surely as the pull 0 above it --
// and neither moves a bound. §28.12.2 gives the strong conflict "the strength
// levels of both signals and all the smaller strength levels", so the range
// already runs to high impedance on both sides, and rule c returns it whole
// each time: rule a keeps every level above the weaker driver, rule b takes the
// rest, and the gap that leaves crosses high impedance and is filled back. A
// second combination cannot narrow what the first left.
TEST(StrengthResolution, SecondWeakerDriverBelowTheFirstWidensNothing) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(arena, {{0, Strength::kStrong},
                                         {1, Strength::kStrong},
                                         {0, Strength::kPull},
                                         {0, Strength::kWeak}});

  ExpectResolvedStrengthsAndX(sn, Strength::kStrong, Strength::kHighz,
                              Strength::kStrong, Strength::kHighz);
}

// The two weaker drivers are of opposite value at one level, so §28.12.3 has a
// combination to make for each, and neither changes the range: §28.12.1 has the
// stronger signal "dominate all the weaker drivers and determine the result",
// and the strong conflict is stronger than both. Rules a and b take the pull
// levels out of the range and rule c puts them back, the gap between the
// surviving 0-side and 1-side levels crossing high impedance (Figure 28-23), so
// the net stands at the conflict range §28.12.2 gave it.
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

// The same two weaker drivers at one value. Each is combined, and the second
// leaves the bounds the first put there: §28.12.3 resolves a level against the
// unambiguous signal it agrees with to whichever of the two is stronger, and
// the two are the same level. A combination of several signals has to be
// idempotent in the signal it repeats, or a net would resolve differently for
// carrying a driver twice.
TEST(StrengthResolution, SameValueWeakerDriversAtOneLevelCombineIdempotently) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(arena, {{0, Strength::kStrong},
                                         {1, Strength::kStrong},
                                         {0, Strength::kPull},
                                         {0, Strength::kPull}});

  ExpectResolvedStrengthsAndX(sn, Strength::kStrong, Strength::kHighz,
                              Strength::kStrong, Strength::kHighz);
}

// A weaker driver at the high-impedance level. §21.2.1.4 says that level
// "cannot have a known logic value" and that the only logic value allowed for
// it is z, so it is not the signal of known value and unambiguous strength
// §28.12.3 combines with, and §28.12.1 has the conflict dominate it. The
// conflict range §28.12.2 gave -- strong down to high impedance on both sides
// -- therefore stands. Running the rules with the level itself, as though a
// high-impedance driver were a signal at strength 0, would instead take the
// 1-side lower bound up to small.
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

// Rule a) at the top of the strength scale: an opposite-value supply-strength
// conflict yields an ambiguous range whose high end is supply, and a weaker
// strong unambiguous driver leaves it there. Rule b takes the levels at or
// below strong and rule c returns them, the gap crossing high impedance, so
// what the case pins is that the maximum level survives net.Resolve and that a
// weaker driver moves neither bound.
TEST(StrengthResolution, RuleAKeepsSupplyLevelAtTopOfScale) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(
      arena,
      {{0, Strength::kSupply}, {1, Strength::kSupply}, {0, Strength::kStrong}});

  ExpectResolvedStrengthsAndX(sn, Strength::kSupply, Strength::kHighz,
                              Strength::kSupply, Strength::kHighz);
  EXPECT_TRUE(sn.net.resolved_strength.IsAmbiguous());
}

// Rule b) complete elimination on the value-1 branch: a stronger unambiguous
// driver of value 1 removes every level of a wholly weaker ambiguous signal,
// collapsing the result to an unambiguous value 1 at the driver's strength.
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

// §28.12.3 through the production combiner rather than through the model beside
// it. Net::Resolve reaches CombineAmbigWithUnambig only after two equally
// strong drivers of opposite value have made an ambiguous signal, and §28.12.2
// gives such a signal every level below the conflict, so it runs to high
// impedance on both sides and the combination returns it unchanged. The
// one-sided range Figure 28-23 draws -- what a three-state gate with an unknown
// control outputs -- is the shape the combination decides, and calling the
// combiner directly is what puts it in front of it.

// §28.12.3 rule c: an ambiguous 1-side range of [supply, supply] against an
// unambiguous 0 at pull leaves a gap between pull and supply, and the signals
// are of opposite value, so the gap belongs to the result. Figure 28-23 draws
// that gap crossing high impedance -- its result is one range running Pu0
// through HiZ to St1 -- so both sides come back reaching high impedance rather
// than the [supply, supply] and [pull, pull] rules a and b alone would leave.
TEST(NetStrengthAmbigUnambig, RuleCFillsTheGapOnTheOppositeValueSide) {
  NetStrength ambig;
  ambig.s1_hi = Strength::kSupply;
  ambig.s1_lo = Strength::kSupply;
  NetStrength r = CombineAmbigWithUnambig(ambig, /*vu=*/0, /*su=*/5);
  EXPECT_EQ(r.s1_hi, Strength::kSupply);
  EXPECT_EQ(r.s1_lo, Strength::kHighz);
  EXPECT_EQ(r.s0_hi, Strength::kPull);
  EXPECT_EQ(r.s0_lo, Strength::kHighz);
}

// §28.12.3 rule c over more than one level: the same shape with the unambiguous
// signal at weak leaves every level between it and the surviving strong in the
// result, and the run does not stop at weak. A gap fill bounded by the
// unambiguous level would report large here and one bounded by the survivor
// alone would report strong.
TEST(NetStrengthAmbigUnambig, RuleCFillsAGapOfSeveralLevels) {
  NetStrength ambig;
  ambig.s1_hi = Strength::kSupply;
  ambig.s1_lo = Strength::kStrong;
  NetStrength r = CombineAmbigWithUnambig(ambig, /*vu=*/0, /*su=*/3);
  EXPECT_EQ(r.s1_hi, Strength::kSupply);
  EXPECT_EQ(r.s1_lo, Strength::kHighz);
}

// §28.12.3 on the side of the unambiguous signal's own value: the two signals
// agree, so each level the ambiguous signal might have settles against the
// unambiguous one at whichever is stronger. Every level of [strong, supply] is
// stronger than the weak the unambiguous signal drives at, so weak cannot be
// the answer to any of them and the result begins at strong. This is the case
// the resolver cannot present, and a combiner anchoring the side at the
// unambiguous level regardless reports weak.
TEST(NetStrengthAmbigUnambig, SameValueRangeAboveTheUnambiguousLevelKeepsIt) {
  NetStrength ambig;
  ambig.s0_hi = Strength::kSupply;
  ambig.s0_lo = Strength::kStrong;
  NetStrength r = CombineAmbigWithUnambig(ambig, /*vu=*/0, /*su=*/3);
  EXPECT_EQ(r.s0_hi, Strength::kSupply);
  EXPECT_EQ(r.s0_lo, Strength::kStrong);
  EXPECT_EQ(r.s1_hi, Strength::kHighz);
}

// §28.12.3 on the same side again, with the ambiguous range straddling the
// unambiguous level: the levels below it resolve to it and the levels above it
// stand, so the result runs from the unambiguous level to the ambiguous top.
// Together with the case above this fixes the lower bound at the greater of the
// two rather than at either one of them.
TEST(NetStrengthAmbigUnambig, SameValueRangeStraddlingTheUnambiguousLevel) {
  NetStrength ambig;
  ambig.s0_hi = Strength::kSupply;
  ambig.s0_lo = Strength::kSmall;
  NetStrength r = CombineAmbigWithUnambig(ambig, /*vu=*/0, /*su=*/3);
  EXPECT_EQ(r.s0_hi, Strength::kSupply);
  EXPECT_EQ(r.s0_lo, Strength::kWeak);
}

// §28.12.3 rule b in full: an ambiguous side lying entirely at or below the
// unambiguous level disappears, so an opposite-value range that reaches only
// weak against an unambiguous strong leaves nothing behind and the result is
// the unambiguous signal alone.
TEST(NetStrengthAmbigUnambig, OppositeValueRangeAtOrBelowSuDisappears) {
  NetStrength ambig;
  ambig.s1_hi = Strength::kWeak;
  ambig.s1_lo = Strength::kSmall;
  NetStrength r = CombineAmbigWithUnambig(ambig, /*vu=*/0, /*su=*/6);
  EXPECT_EQ(r.s1_hi, Strength::kHighz);
  EXPECT_EQ(r.s1_lo, Strength::kHighz);
  EXPECT_EQ(r.s0_hi, Strength::kStrong);
  EXPECT_EQ(r.s0_lo, Strength::kStrong);
}

// §28.12.3 with the unambiguous signal driving 1 rather than 0: the rules are
// stated of the two sides by value and not by position, so the mirror of the
// rule c case above gives the mirrored answer. A combiner reading the sides by
// position passes the cases above and fails this one.
TEST(NetStrengthAmbigUnambig, RulesFollowTheValueAndNotTheSide) {
  NetStrength ambig;
  ambig.s0_hi = Strength::kSupply;
  ambig.s0_lo = Strength::kSupply;
  NetStrength r = CombineAmbigWithUnambig(ambig, /*vu=*/1, /*su=*/5);
  EXPECT_EQ(r.s0_hi, Strength::kSupply);
  EXPECT_EQ(r.s0_lo, Strength::kHighz);
  EXPECT_EQ(r.s1_hi, Strength::kPull);
  EXPECT_EQ(r.s1_lo, Strength::kHighz);
}

// §28.12.3 rule c where the ambiguous signal is stronger than the unambiguous
// one throughout. §28.12.1 has the stronger signal "dominate all the weaker
// drivers and determine the result", and the weak level the unambiguous signal
// drives at is in no part of the result -- but the levels it removed are, since
// rule c's gap is bounded by the surviving pieces and those sit on opposite
// sides of the scale. Both sides therefore come back reaching high impedance,
// and the combination has widened nothing that the ambiguous signal's own range
// did not already admit.
//
// The input is one Net::Resolve cannot present: §28.12.2 gives a conflict every
// level below its own, so an ambiguous signal it builds runs to high impedance
// on both sides. The case is about the function.
TEST(NetStrengthAmbigUnambig, DominatingAmbiguousSignalKeepsItsOwnRange) {
  NetStrength ambig;
  ambig.s0_hi = Strength::kStrong;
  ambig.s0_lo = Strength::kPull;
  ambig.s1_hi = Strength::kStrong;
  ambig.s1_lo = Strength::kStrong;
  NetStrength r = CombineAmbigWithUnambig(ambig, /*vu=*/1, /*su=*/3);
  EXPECT_EQ(r.s0_hi, Strength::kStrong);
  EXPECT_EQ(r.s0_lo, Strength::kHighz);
  EXPECT_EQ(r.s1_hi, Strength::kStrong);
  EXPECT_EQ(r.s1_lo, Strength::kHighz);
}

// §28.12.3 driven from source. Nothing above reaches Net::Resolve the way a
// design does: the two cases below state their nets as continuous assignments
// carrying the drive strength specifications of §28.11, so the strengths the
// lowerer hands the resolver are the ones the source names.
//
// Only the opposite-value shape is read back through %v, and its four bounds
// are asserted beside the rendering. §21.2.1.4 names the strength characters
// of an unknown value from one level per side -- Table 21-5 reads "65X" as "an
// unknown value with a strong driving 0 component and a pull driving 1
// component" -- and §28.12.3 rule a keeps the strongest level of each side
// whatever the weaker drivers do, so the levels that clause names never move
// here. The rendering therefore does not separate a folded result from an
// unfolded one at all: FormatStrength reaches for the mnemonic when the two
// sides' strongest levels are equal, which they are either way. What the
// rendering says is that the strength reached %v as the resolver left it; what
// says the weaker drivers were combined is the four bounds asserted beside it,
// and for every other shape in this file the rendering is the same whether they
// were combined or dropped, so a case reading it alone would pass on the
// behavior and on its absence alike -- which
// .claude/memories/discriminating-test-inputs.md rules out. The bounds stand
// beside the rendering for the same reason: they are what §28.12.3 decides, and
// they say so whatever the renderer does with them.
//
// FormatStrength is the function §21.2.1.4's %v dispatches to
// (src/simulator/eval_system_task.cpp), so the assertion names the whole
// three-character string rather than searching a captured line for it.
//
// A large capacitor strength cannot appear in either source. §28.11 makes
// large, medium and small the charge storage strengths of a trireg, and the
// driving strengths a continuous assignment can name are supply, strong, pull
// and weak.

// Two weaker drivers of opposite value at one level, from source. Both are
// combined and neither moves a bound: the strong conflict runs to high
// impedance on both sides (§28.12.2) and rule c returns every level rule b
// takes, the gap between the surviving sides crossing high impedance. §21.2.1.4
// renders the result with the mnemonic of the two sides' strongest level and
// the unknown logic value -- StX -- since it names one level per side and this
// result's strongest levels are equal. The four bounds are asserted beside the
// rendering because the rendering reads the strongest levels alone and would
// say StX whatever the weaker drivers did to the low ends.
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

// A driver at the high-impedance level from source, which only a strength
// specification can state: §28.11 makes (highz0, highz1) illegal, so the 1
// side carries a driving strength and the assignment drives a 0, leaving the
// driver at highz0. It combines to nothing and the conflict range stands.
TEST(StrengthResolution, SourceHighzStrengthDriverLeavesTheConflictRangeWhole) {
  NetStrength ns = ResolveSrcNetW(
      ConflictPlusWeakerSrc("  assign (highz0, strong1) w = 1'b0;\n"));
  EXPECT_EQ(ns.s0_hi, Strength::kStrong);
  EXPECT_EQ(ns.s0_lo, Strength::kHighz);
  EXPECT_EQ(ns.s1_hi, Strength::kStrong);
  EXPECT_EQ(ns.s1_lo, Strength::kHighz);
}

// --- §28.12.3's own figures ---
//
// The clause states rules a), b) and c) in words that leave what rule c's gap
// runs to open, and draws four combinations that answer it. Each case below is
// one of those drawings, so the reading the two implementations share is
// anchored to the standard rather than to either of them.

// Figure 28-23: an ambiguous signal occupying the strength1 side from high
// impedance to strong -- what §28.12.2's Figure 28-6 gives a three-state gate
// with an unknown control -- combined with an unambiguous Pu0. The figure draws
// one range running Pu0 through HiZ0 and HiZ1 to St1, and its prose calls it "a
// range defined by the greatest strength in the range of the ambiguous strength
// signal and by the strength level of the unambiguous strength signal". Rule
// c's gap therefore crosses high impedance: a fill bounded by the unambiguous
// level would leave the 1 side at strong and the 0 side at pull.
TEST(NetStrengthAmbigUnambig, Figure2823FillsAcrossHighImpedance) {
  NetStrength ambig;
  ambig.s1_hi = Strength::kStrong;
  ambig.s1_lo = Strength::kHighz;
  NetStrength r = CombineAmbigWithUnambig(ambig, /*vu=*/0, /*su=*/5);
  EXPECT_EQ(r.s0_hi, Strength::kPull);
  EXPECT_EQ(r.s0_lo, Strength::kHighz);
  EXPECT_EQ(r.s1_hi, Strength::kStrong);
  EXPECT_EQ(r.s1_lo, Strength::kHighz);
}

// Figure 28-22: the same side for both signals, so no gap of opposite value
// opens and rules a) and b) alone decide. The ambiguous 1 range runs from high
// impedance to pull and the unambiguous Me1 stands at medium, and the figure
// draws the result from Me1 to Pu1 -- the levels below medium disappear rather
// than being filled back.
TEST(NetStrengthAmbigUnambig, Figure2822StopsAtTheUnambiguousLevel) {
  NetStrength ambig;
  ambig.s1_hi = Strength::kPull;
  ambig.s1_lo = Strength::kHighz;
  NetStrength r = CombineAmbigWithUnambig(ambig, /*vu=*/1, /*su=*/2);
  EXPECT_EQ(r.s1_hi, Strength::kPull);
  EXPECT_EQ(r.s1_lo, Strength::kMedium);
  EXPECT_EQ(r.s0_hi, Strength::kHighz);
  EXPECT_EQ(r.s0_lo, Strength::kHighz);
}

// Figure 28-20, which the clause names as rule b) on its own: an ambiguous 0
// range against an unambiguous 0 at pull keeps the levels above pull and takes
// the rest, leaving the range the figure draws from Pu0 to St0.
TEST(NetStrengthAmbigUnambig, Figure2820EliminatesTheLevelsAtOrBelowSu) {
  NetStrength ambig;
  ambig.s0_hi = Strength::kStrong;
  ambig.s0_lo = Strength::kHighz;
  NetStrength r = CombineAmbigWithUnambig(ambig, /*vu=*/0, /*su=*/5);
  EXPECT_EQ(r.s0_hi, Strength::kStrong);
  EXPECT_EQ(r.s0_lo, Strength::kPull);
  EXPECT_EQ(r.s1_hi, Strength::kHighz);
}

// Figure 28-21: an ambiguous signal crossing the scale, whose opposite-value
// component lies entirely below the unambiguous Pu1. Nothing of the opposite
// value survives rule b), so rule c) has no gap to fill and the result is the
// range the figure draws, from the unambiguous level to the ambiguous signal's
// greater extreme.
TEST(NetStrengthAmbigUnambig, Figure2821LeavesTheRangeFromSuToTheExtreme) {
  NetStrength ambig;
  ambig.s0_hi = Strength::kWeak;
  ambig.s0_lo = Strength::kHighz;
  ambig.s1_hi = Strength::kStrong;
  ambig.s1_lo = Strength::kHighz;
  NetStrength r = CombineAmbigWithUnambig(ambig, /*vu=*/1, /*su=*/5);
  EXPECT_EQ(r.s1_hi, Strength::kStrong);
  EXPECT_EQ(r.s1_lo, Strength::kPull);
  EXPECT_EQ(r.s0_hi, Strength::kHighz);
  EXPECT_EQ(r.s0_lo, Strength::kHighz);
}

// --- the model and the function it models, on one input ---
//
// A model under lib/cpp/test_models/ states what the standard requires
// independently of the code, so a case can be checked against the clause rather
// than against the implementation. That is worth only as much as the two
// agreeing, and nothing ran them on one input: the cases above call one or the
// other. These two do, over the inputs where a divergence would show.

// The four bounds a combination answers with, in the order §21.2.1.4 reads
// them: the strength0 side and then the strength1 side, each from its strongest
// level to its weakest.
struct ExpectedBounds {
  StrengthLevel s0_hi;
  StrengthLevel s0_lo;
  StrengthLevel s1_hi;
  StrengthLevel s1_lo;
};

// Those bounds read off both the model and the production combiner for one
// ambiguous signal and one unambiguous (value, level) pair, so a case states
// the clause's answer once and both implementations are held to it.
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

// Figure 28-23's own input, which is where the two used to differ: each filled
// the opposite side down to one level above the unambiguous signal, and both
// stopped short of the high impedance the figure draws.
TEST(NetStrengthAmbigUnambig, ModelAndCombinerAgreeOnFigure2823) {
  ExpectModelAndCombinerAgree(
      AmbiguousRange(Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kStrong),
      Val4::kV0, StrengthLevel::kPull,
      {StrengthLevel::kPull, StrengthLevel::kHighz, StrengthLevel::kStrong,
       StrengthLevel::kHighz});
}

// The shape Net::Resolve actually builds: §28.12.2's conflict range, which runs
// to high impedance on both sides, against a weaker unambiguous driver. The
// combination returns it unchanged, and the two implementations say so alike.
TEST(NetStrengthAmbigUnambig, ModelAndCombinerAgreeOnAResolverConflictRange) {
  ExpectModelAndCombinerAgree(
      AmbiguousRange(Val4::kX, StrengthLevel::kHighz, StrengthLevel::kStrong),
      Val4::kV0, StrengthLevel::kPull,
      {StrengthLevel::kStrong, StrengthLevel::kHighz, StrengthLevel::kStrong,
       StrengthLevel::kHighz});
}

// The same-value side, where no gap opens: the two agree there too, so the
// agreement above is not one the fill alone accounts for.
TEST(NetStrengthAmbigUnambig, ModelAndCombinerAgreeWithNoOppositeSurvivor) {
  ExpectModelAndCombinerAgree(
      AmbiguousRange(Val4::kV0, StrengthLevel::kHighz, StrengthLevel::kStrong),
      Val4::kV0, StrengthLevel::kPull,
      {StrengthLevel::kStrong, StrengthLevel::kPull, StrengthLevel::kHighz,
       StrengthLevel::kHighz});
}

}  // namespace
