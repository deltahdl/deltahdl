#pragma once

#include <gtest/gtest.h>

#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

struct CapacitivePair {
  Net* from;
  Net* to;
};

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
  EXPECT_EQ(me1->charge_strength, me2->charge_strength);

  me1->resolved->value = MakeLogic4VecVal(f.arena, 1, from_value);
  me2->resolved->value = MakeLogic4VecVal(f.arena, 1, to_value);
  return {me1, me2};
}
