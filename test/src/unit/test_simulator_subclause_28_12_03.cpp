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
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kStrong);
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
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kPull);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kPull);
}

TEST(StrengthCombineAmbigUnambig, RuleCFillsMultiLevelGap) {
  StrengthSignal unambig = UnambiguousSignal(Val4::kV0, StrengthLevel::kWeak);
  StrengthSignal ambig =
      AmbiguousRange(Val4::kV1, StrengthLevel::kStrong, StrengthLevel::kSupply);
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kSupply);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kLarge);
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
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kPull);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kStrong);
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
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kPull);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kStrong);
}

TEST(StrengthCombineAmbigUnambig, RuleCFillsGapOnOppositeSideMirror) {
  StrengthSignal unambig = UnambiguousSignal(Val4::kV1, StrengthLevel::kPull);
  StrengthSignal ambig =
      AmbiguousRange(Val4::kV0, StrengthLevel::kSupply, StrengthLevel::kSupply);
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kSupply);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kPull);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kPull);
}

TEST(StrengthCombineAmbigUnambig, HighZUnambigPreservesEntireAmbig) {
  StrengthSignal unambig = UnambiguousSignal(Val4::kV0, StrengthLevel::kHighz);
  StrengthSignal ambig =
      AmbiguousRange(Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kPull);
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kPull);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kSmall);
}

TEST(StrengthResolution, RuleAAndBTrimAmbigLoBoundsPerSide) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(
      arena,
      {{0, Strength::kPull}, {1, Strength::kPull}, {0, Strength::kWeak}});

  ExpectResolvedStrengthsAndX(sn, Strength::kPull, Strength::kWeak,
                              Strength::kPull, Strength::kLarge);
}

TEST(StrengthResolution, RuleAAndBTrimAmbigLoBoundsPerSideVuOne) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(
      arena,
      {{0, Strength::kStrong}, {1, Strength::kStrong}, {1, Strength::kWeak}});

  ExpectResolvedStrengthsAndX(sn, Strength::kStrong, Strength::kLarge,
                              Strength::kStrong, Strength::kWeak);
  EXPECT_TRUE(sn.net.resolved_strength.IsAmbiguous());
}

TEST(StrengthResolution, RuleBAtAmbigHiMinusOnePerSide) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(
      arena,
      {{0, Strength::kStrong}, {1, Strength::kStrong}, {0, Strength::kPull}});

  ExpectResolvedStrengthsAndX(sn, Strength::kStrong, Strength::kPull,
                              Strength::kStrong, Strength::kStrong);
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
// and it moves no bound. §28.12.1 has the stronger signal dominate the weaker,
// and after the pull 0 has been combined the result holds no level at or below
// weak for the weak 0 to be the lower bound of: rule c's gap needs the
// unambiguous signal's own level to bound it from below, and that level is not
// in the result. A combination that filled the gap regardless would take the 1
// side down to large and report the net at levels no driver drives it to.
TEST(StrengthResolution, SecondWeakerDriverBelowTheFirstWidensNothing) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(arena, {{0, Strength::kStrong},
                                         {1, Strength::kStrong},
                                         {0, Strength::kPull},
                                         {0, Strength::kWeak}});

  ExpectResolvedStrengthsAndX(sn, Strength::kStrong, Strength::kPull,
                              Strength::kStrong, Strength::kStrong);
}

// The shape a second combination decides. The two weaker drivers are of
// opposite value at one level, so neither dominates the other and §28.12.3 has
// a combination to make for each: the pull 0 leaves the 1 side only the levels
// above pull (rules a and b), and the pull 1 leaves the 0 side only the levels
// above pull. Combining only the strongest of them leaves the 0 side reaching
// to pull, a level the drivers do not admit. The result carries a single level
// on each side, so the net is a strong x of unambiguous strength -- Table
// 21-5's StX -- rather than a range.
TEST(StrengthResolution, OppositeValueWeakerDriversAtOneLevelBothCombine) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(arena, {{0, Strength::kStrong},
                                         {1, Strength::kStrong},
                                         {0, Strength::kPull},
                                         {1, Strength::kPull}});

  ExpectResolvedStrengthsAndX(sn, Strength::kStrong, Strength::kStrong,
                              Strength::kStrong, Strength::kStrong);
  EXPECT_FALSE(sn.net.resolved_strength.IsAmbiguous());
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

  ExpectResolvedStrengthsAndX(sn, Strength::kStrong, Strength::kPull,
                              Strength::kStrong, Strength::kStrong);
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

  ExpectResolvedStrengthsAndX(sn, Strength::kPull, Strength::kSmall,
                              Strength::kPull, Strength::kMedium);
}

// Rule a) at the top of the strength scale: an opposite-value supply-strength
// conflict yields an ambiguous range whose high end is supply; a weaker strong
// unambiguous driver leaves the supply level in place (rule a) while trimming
// the levels at or below strong (rule b). Exercises preservation of the maximum
// strength level through net.Resolve.
TEST(StrengthResolution, RuleAKeepsSupplyLevelAtTopOfScale) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(
      arena,
      {{0, Strength::kSupply}, {1, Strength::kSupply}, {0, Strength::kStrong}});

  // Unambiguous side (value 0) extends down to the unambiguous strong level;
  // the opposite side keeps only the supply level above strong.
  ExpectResolvedStrengthsAndX(sn, Strength::kSupply, Strength::kStrong,
                              Strength::kSupply, Strength::kSupply);
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
// strong drivers of opposite value have made an ambiguous signal, and such a
// signal always runs down to highz, so the resolver cannot present an ambiguous
// range that begins above the unambiguous level -- which is where rules b and c
// have anything to decide. Calling the combiner directly is what puts those
// ranges in front of it.

// §28.12.3 rule c: an ambiguous 1-side range of [supply, supply] against an
// unambiguous 0 at pull leaves a gap between pull and supply, and the signals
// are of opposite value, so the gap belongs to the result. The range comes back
// [strong, supply] rather than the [supply, supply] rules a and b alone would
// leave, and rule c is the only thing that lowers the bound.
TEST(NetStrengthAmbigUnambig, RuleCFillsTheGapOnTheOppositeValueSide) {
  NetStrength ambig;
  ambig.s1_hi = Strength::kSupply;
  ambig.s1_lo = Strength::kSupply;
  NetStrength r = CombineAmbigWithUnambig(ambig, /*vu=*/0, /*su=*/5);
  EXPECT_EQ(r.s1_hi, Strength::kSupply);
  EXPECT_EQ(r.s1_lo, Strength::kStrong);
  EXPECT_EQ(r.s0_hi, Strength::kPull);
  EXPECT_EQ(r.s0_lo, Strength::kPull);
}

// §28.12.3 rule c over more than one level: the same shape with the unambiguous
// signal at weak leaves four levels between it and the surviving strong, and
// every one of them is in the result. A gap fill that reached only one level
// below the survivor would report large here.
TEST(NetStrengthAmbigUnambig, RuleCFillsAGapOfSeveralLevels) {
  NetStrength ambig;
  ambig.s1_hi = Strength::kSupply;
  ambig.s1_lo = Strength::kStrong;
  NetStrength r = CombineAmbigWithUnambig(ambig, /*vu=*/0, /*su=*/3);
  EXPECT_EQ(r.s1_hi, Strength::kSupply);
  EXPECT_EQ(r.s1_lo, Strength::kLarge);
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
  EXPECT_EQ(r.s0_lo, Strength::kStrong);
  EXPECT_EQ(r.s1_hi, Strength::kPull);
  EXPECT_EQ(r.s1_lo, Strength::kPull);
}

// §28.12.3 rule c against a signal that dominates the unambiguous one. Every
// level of this ambiguous signal is stronger than the weak the unambiguous
// signal drives at, so by §28.12.1 the stronger signal dominates the weaker
// and the weak level is in no part of the result. Rule c's gap is bounded from
// below by that level, so there is no gap: the levels beneath the surviving
// ones lie under nothing. The 0-side bound therefore stays where rules a and b
// left it, at pull, and a gap fill that ran regardless would take it to large.
//
// This is the shape a net presents to the second of two combinations, which is
// why it decides whether combining every weaker driver widens the result or
// leaves it alone.
TEST(NetStrengthAmbigUnambig, DominatedUnambigSignalOpensNoGapToFill) {
  NetStrength ambig;
  ambig.s0_hi = Strength::kStrong;
  ambig.s0_lo = Strength::kPull;
  ambig.s1_hi = Strength::kStrong;
  ambig.s1_lo = Strength::kStrong;
  NetStrength r = CombineAmbigWithUnambig(ambig, /*vu=*/1, /*su=*/3);
  EXPECT_EQ(r.s0_hi, Strength::kStrong);
  EXPECT_EQ(r.s0_lo, Strength::kPull);
  EXPECT_EQ(r.s1_hi, Strength::kStrong);
  EXPECT_EQ(r.s1_lo, Strength::kStrong);
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
// behavior and on its absence alike -- which the "Tests" section of
// CLAUDE.md rules out.
// The bounds stand beside the rendering for the same reason: they are what
// §28.12.3 decides, and they say so whatever the renderer does with them.
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
// combined, so each side of the result carries the single level strong, which
// §21.2.1.4 renders with that level's mnemonic and the unknown logic value:
// StX. Combining only the strongest of them leaves the 0 side running down to
// pull, and renders StX as well -- §21.2.1.4 chooses the mnemonic when the two
// sides' strongest levels are equal, which rule a keeps them either way. The
// four bounds asserted below are what separates the two, and the rendering is
// asserted beside them to say that the strength reaches %v as the resolver
// left it.
TEST(StrengthResolution, SourceOppositeValuePullDriversRenderAsStX) {
  NetStrength ns = ResolveSrcNetW(
      ConflictPlusWeakerSrc("  assign (pull0, pull1) w = 1'b0;\n"
                            "  assign (pull0, pull1) w = 1'b1;\n"));
  EXPECT_EQ(ns.s0_hi, Strength::kStrong);
  EXPECT_EQ(ns.s0_lo, Strength::kStrong);
  EXPECT_EQ(ns.s1_hi, Strength::kStrong);
  EXPECT_EQ(ns.s1_lo, Strength::kStrong);
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

}  // namespace
