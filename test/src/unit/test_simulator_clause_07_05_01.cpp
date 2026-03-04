#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/adv_sim.h"

using namespace delta;

namespace {

TEST(AdvSim, DynArrayPushAndAccess) {
  DynArray arr;
  arr.Push(42);
  arr.Push(99);
  EXPECT_EQ(arr.Size(), 2u);
  EXPECT_EQ(arr.At(0), 42u);
  EXPECT_EQ(arr.At(1), 99u);
}

}
