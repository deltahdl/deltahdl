#pragma once

#include "fixture_simulator.h"
#include "gtest/gtest.h"

using namespace delta;

// Populate an existing integer-keyed assoc array with the three entries
// {1:10, 2:20, 3:30} and assert that the size and each stored value are
// correct. Shared by the wildcard- and integral-index MultipleKeys tests,
// which differ only in how the array under test is created.
inline void FillAndCheckThreeKeys(SimFixture& f, AssocArrayObject* aa) {
  aa->int_data[1] = MakeLogic4VecVal(f.arena, 32, 10);
  aa->int_data[2] = MakeLogic4VecVal(f.arena, 32, 20);
  aa->int_data[3] = MakeLogic4VecVal(f.arena, 32, 30);

  EXPECT_EQ(aa->Size(), 3u);
  EXPECT_EQ(aa->int_data[1].ToUint64(), 10u);
  EXPECT_EQ(aa->int_data[2].ToUint64(), 20u);
  EXPECT_EQ(aa->int_data[3].ToUint64(), 30u);
}
