#pragma once

#include "common/types.h"
#include "fixture_simulator.h"
#include "gtest/gtest.h"
#include "simulator/sim_context_types.h"

using namespace delta;

inline void FillAndCheckThreeKeys(SimFixture& f, AssocArrayObject* aa) {
  aa->int_data[1] = MakeLogic4VecVal(f.arena, 32, 10);
  aa->int_data[2] = MakeLogic4VecVal(f.arena, 32, 20);
  aa->int_data[3] = MakeLogic4VecVal(f.arena, 32, 30);

  EXPECT_EQ(aa->Size(), 3u);
  EXPECT_EQ(aa->int_data[1].ToUint64(), 10u);
  EXPECT_EQ(aa->int_data[2].ToUint64(), 20u);
  EXPECT_EQ(aa->int_data[3].ToUint64(), 30u);
}
