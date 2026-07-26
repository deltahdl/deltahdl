#pragma once

#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

// A pair of capacitive nets a charge-decay rule is stated over: the one the
// charge propagates from and the one it propagates to.
struct CapacitivePair {
  Net* from;
  Net* to;
};

// Two trireg nets of equal charge storage size, elaborated from real source
// and each left holding the value the caller names.
//
// A rule about what happens when two charge-storing nets meet needs both nets
// to be in the capacitive state and their sizes to stand in a known relation
// to each other, so this declares both with the same (medium) strength,
// confirms the elaborated nets are capacitive and equally sized, and then
// stores one bit in each. `from_value` and `to_value` are the stored charges
// the rule is then read against.
//
// The fixture is caller-owned, so the arena holding the stored values outlives
// the call.
inline CapacitivePair MakeEqualSizeTriregs(SimFixture& f, uint64_t from_value,
                                           uint64_t to_value) {
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg (medium) me1;\n"
      "  trireg (medium) me2;\n"
      "endmodule\n",
      f);
  EXPECT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* me1 = f.ctx.FindNet("me1");
  auto* me2 = f.ctx.FindNet("me2");
  EXPECT_NE(me1, nullptr);
  EXPECT_NE(me2, nullptr);
  if (me1 == nullptr || me2 == nullptr) return {nullptr, nullptr};
  EXPECT_TRUE(me1->InCapacitiveState());
  EXPECT_TRUE(me2->InCapacitiveState());
  EXPECT_EQ(me1->charge_strength, me2->charge_strength);  // both (medium)

  me1->resolved->value = MakeLogic4VecVal(f.arena, 1, from_value);
  me2->resolved->value = MakeLogic4VecVal(f.arena, 1, to_value);
  return {me1, me2};
}
