#include <gtest/gtest.h>

#include "common/arena.h"
#include "model_strength.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Rule a) baseline: when the ambig signal has its hi above Su, that hi must
// survive on its side. The unambig sits at Su on its own side; the result
// straddles both halves of the strength scale and is therefore x.
TEST(StrengthCombineAmbigUnambig, RuleAPreservesHighEndOfRange) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kSmall,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kWeak};
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kSmall);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kWeak);
}

// Rule a) per-side: a wide ambig range on the !Vu side is trimmed at the
// bottom by Su (rule b) but its hi (rule a) carries through unchanged.
TEST(StrengthCombineAmbigUnambig, RuleATrimsLowEndButKeepsHigh) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kPull,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{Val4::kV1, StrengthLevel::kHighz,
                       StrengthLevel::kStrong};
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kStrong);
}

// Rule b) baseline: when every level of the ambig signal is at or below Su,
// the ambig disappears entirely and the result is the lone unambig signal.
TEST(StrengthCombineAmbigUnambig, RuleBEliminatesAmbigAtOrBelowSu) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kStrong,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kWeak};
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kV0);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kHighz);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kHighz);
}

// Rule b) boundary case: equality (ambig hi == Su) still disappears. The "or
// equal to" half of rule b) is the part that distinguishes §28.12.3 from a
// naive "stronger wins" rule.
TEST(StrengthCombineAmbigUnambig, RuleBEliminatesAmbigAtExactlySu) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kPull,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kPull};
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kV0);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kHighz);
}

// Rule b) with same-value ambig: the unambig still shadows ambig levels at or
// below Su on its own side. The merged Vu-side range starts at Su (from the
// unambig) and extends up to whatever ambig levels survived rule a.
TEST(StrengthCombineAmbigUnambig, RuleBSameValueMergeWithUnambig) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kWeak,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{Val4::kV0, StrengthLevel::kStrong,
                       StrengthLevel::kHighz};
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kV0);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kWeak);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kHighz);
}

// Rule c) baseline: the ambig signal lives only at Supply on the opposite
// side. After rule a/b alone the !Vu side would be a lone Supply with nothing
// at Strong below it — a one-level gap from Pull (Su+1 on the !Vu side after
// rule b would be Strong, but ambig.lo is Supply). Rule c) fills the gap so
// the !Vu side runs Strong..Supply.
TEST(StrengthCombineAmbigUnambig, RuleCFillsGapOnOppositeSide) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kPull,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{
      .value = Val4::kV1,
      .strength0_hi = StrengthLevel::kHighz,
      .strength1_hi = StrengthLevel::kSupply,
      .strength0_lo = StrengthLevel::kHighz,
      .strength1_lo = StrengthLevel::kSupply,
  };
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kSupply);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kPull);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kPull);
}

// Rule c) with a multi-level gap: ambig is a high-only Strong..Supply range
// on the !Vu side. Rule c) must fill all levels between Su and the surviving
// lo, not just the adjacent one. Su is Weak, so the gap fill drops the !Vu
// lo from Strong down to Large.
TEST(StrengthCombineAmbigUnambig, RuleCFillsMultiLevelGap) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kWeak,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{
      .value = Val4::kV1,
      .strength0_hi = StrengthLevel::kHighz,
      .strength1_hi = StrengthLevel::kSupply,
      .strength0_lo = StrengthLevel::kHighz,
      .strength1_lo = StrengthLevel::kStrong,
  };
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kSupply);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kLarge);
}

// Rule c) is opposite-value-only: when surviving ambig is on the SAME side as
// the unambig (same value), no gap-fill takes place because rule c)'s
// "because the signals are of opposite value" precondition is not met.
TEST(StrengthCombineAmbigUnambig, RuleCDoesNotFillSameSideGap) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kWeak,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{
      .value = Val4::kV0,
      .strength0_hi = StrengthLevel::kSupply,
      .strength1_hi = StrengthLevel::kHighz,
      .strength0_lo = StrengthLevel::kStrong,
      .strength1_lo = StrengthLevel::kHighz,
  };
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kV0);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kSupply);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kHighz);
}

// Rule a/b combined across both sides of an ambig signal: a strong x ambig
// (HiZ..Strong on both sides) combined with a Pull-0 unambig must trim both
// sides to (Pull, Strong] — Strong on each side after rule b.
TEST(StrengthCombineAmbigUnambig, RulesAAndBApplyPerSide) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kPull,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{Val4::kX, StrengthLevel::kStrong,
                       StrengthLevel::kStrong};
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kPull);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kStrong);
}

// Edge case: a Supply unambig wipes out every ambig level under any rule.
// Even Supply-strength ambig on the opposite side disappears because rule b)
// uses "smaller than or equal to" — equal still goes.
TEST(StrengthCombineAmbigUnambig, SupplyUnambigWipesAllAmbig) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kSupply,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{Val4::kV1, StrengthLevel::kHighz,
                       StrengthLevel::kSupply};
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kV0);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kSupply);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kHighz);
}

// V1 mirror of the rule a/b/c shape so the rules are checked symmetrically
// regardless of which side the unambig lives on.
TEST(StrengthCombineAmbigUnambig, MirrorWithV1Unambig) {
  StrengthSignal unambig{Val4::kV1, StrengthLevel::kHighz,
                         StrengthLevel::kPull};
  StrengthSignal ambig{Val4::kV0, StrengthLevel::kStrong,
                       StrengthLevel::kHighz};
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kPull);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kPull);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kStrong);
}

// Rule c with V1 unambig: the gap-fill branch is value-asymmetric in the
// implementation (different side selected for filling), so check the V1 leg
// directly rather than infer it from the V0 cases.
TEST(StrengthCombineAmbigUnambig, RuleCFillsGapOnOppositeSideMirror) {
  StrengthSignal unambig{Val4::kV1, StrengthLevel::kHighz,
                         StrengthLevel::kPull};
  StrengthSignal ambig{
      .value = Val4::kV0,
      .strength0_hi = StrengthLevel::kSupply,
      .strength1_hi = StrengthLevel::kHighz,
      .strength0_lo = StrengthLevel::kSupply,
      .strength1_lo = StrengthLevel::kHighz,
  };
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kSupply);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kPull);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kPull);
}

// Edge case: an unambig at kHighz (degenerate Su=0) leaves rule a applying to
// every non-HiZ ambig level. The result should be the original ambig range
// since nothing can be at or below HiZ (rule b removes only the HiZ slots,
// which contribute nothing).
TEST(StrengthCombineAmbigUnambig, HighZUnambigPreservesEntireAmbig) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kHighz,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kPull};
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kPull);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kSmall);
}

// Runtime check: when the ambig signal is materialised by two equal-strength
// opposite-value drivers (which §28.12.2 says yields x with the shared
// strength), and a third unambig driver of higher strength is added, the
// per-bit value at the resolved net is the unambig driver's value. This is
// the value-only consequence of rule b) eliminating the ambig levels at or
// below Su.
TEST(StrengthResolution, AmbigUnderStrongerUnambigYieldsUnambigValue) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// Rule a) at the runtime: when a weaker unambig sits below an ambig formed
// by an equal-strength conflict, the per-side hi must remain at the conflict
// level (§28.12.2 R1 strength) and the per-side lo must rise from kHighz to
// the level required by rule a/b. Vu side merges down to Su (the unambig's
// level); !Vu side trims to Su+1 (the smallest level not removed by rule b).
TEST(StrengthResolution, RuleAAndBTrimAmbigLoBoundsPerSide) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kWeak);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kLarge);
  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

// Mirror of the above with Vu=1: confirms rules a/b apply symmetrically. The
// !Vu side (side 0) must clamp its lo at Su+1 (Large) and the Vu side
// (side 1) must extend its lo down to Su (Weak) where the unambig sits.
TEST(StrengthResolution, RuleAAndBTrimAmbigLoBoundsPerSideVuOne) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kLarge);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kWeak);
  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
  EXPECT_TRUE(net.resolved_strength.IsAmbiguous());
}

// Rule b) at Su = ambig hi - 1: when the unambig sits one level below the
// conflict's strength, rule a leaves only the conflict level on the !Vu side
// (lo = hi = Strong) and the Vu-side lo extends down to Su (Pull). This pins
// the boundary case where rule a's surviving range collapses to a single
// level on the !Vu side.
TEST(StrengthResolution, RuleBAtAmbigHiMinusOnePerSide) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kStrong);
  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
  EXPECT_TRUE(net.resolved_strength.IsAmbiguous());
}

// Per-bit independence at runtime: rules a/b apply at each bit position
// separately. Two equal-strength conflicting drivers (which §28.12.2 makes an
// ambiguous signal) plus a Strong-1 driver: the Strong driver dominates only
// the bits where it contributes a non-z value. Drive 0xA on the Strong-1 line
// (value 0b1010) and conflict pattern 0xC vs 0x3 on the Pull lines. The
// Strong driver's value should win on every bit (since Strong > Pull at every
// bit position), demonstrating rule b's per-bit application.
TEST(StrengthResolution, AmbigUnambigPerBitIndependence) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 4);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b1100));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b0011));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b1010));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64() & 0xFu, 0b1010u);
}

// Rule b)'s complete-elimination outcome: when the unambig sits at or above
// the ambig hi on both sides, every ambig level disappears and the result
// collapses to the unambig alone. Pairs strength assertions with the
// existing value-only AmbigUnderStronger… check so that the post-§28.12.3
// state — single-level on the Vu side, kHighz on the !Vu side, no longer
// ambiguous — is also pinned at the runtime.
TEST(StrengthResolution, RuleBCompleteEliminationProducesUnambigResult) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kHighz);
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// When more than one unambig driver sits below the conflict, §28.12.3 must
// be applied with the *strongest* of them as the single-level component:
// rule a's surviving range and rule b's lo trim are both anchored at that
// Su. Drives Pull-0 (the strongest weaker) alongside Weak-0 to detect a
// regression that picks a different weaker driver — picking Weak-0 would
// drop the Vu-side lo to Weak instead of Pull.
TEST(StrengthResolution, StrongestWeakerUnambigSelectedForRuleApplication) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kStrong);
  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

// Rule b's "<=Su" inequality at the smallest non-kHighz level: pins the low
// end of the strength scale so a regression that special-cased kSmall (e.g.
// treating Su=Small as Su=HiZ and skipping the trim) would be caught. The
// !Vu-side lo must rise from kHighz to kMedium (Su+1) and the Vu-side lo
// must extend down to kSmall (Su) where the unambig contributes.
TEST(StrengthResolution, RuleAAndBAtSmallestNonHighzSu) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kSmall, Strength::kSmall});
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kSmall);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kMedium);
  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

// Net-type independence: §28.12.3 fires on any net whose resolution path
// folds drivers — kTri must produce the same per-side trimmed range as
// kWire when the same drivers are present. Guards against a regression
// that gates the §28.12.3 application on the wire branch.
TEST(StrengthResolution, RuleAAndBApplyOnTriNet) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTri;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kWeak);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kLarge);
  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

}  // namespace
