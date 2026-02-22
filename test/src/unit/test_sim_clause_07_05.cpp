// §7.5: Dynamic arrays

#include <gtest/gtest.h>
#include <cstdint>
#include <string>
#include "common/arena.h"
#include "common/types.h"
#include "simulation/adv_sim.h"

using namespace delta;

namespace {

// =============================================================================
// DynArray
// =============================================================================
TEST(AdvSim, DynArrayDefaultEmpty) {
  DynArray arr;
  EXPECT_EQ(arr.Size(), 0u);
}

TEST(AdvSim, DynArrayPushAndAccess) {
  DynArray arr;
  arr.Push(42);
  arr.Push(99);
  EXPECT_EQ(arr.Size(), 2u);
  EXPECT_EQ(arr.At(0), 42u);
  EXPECT_EQ(arr.At(1), 99u);
}

TEST(AdvSim, DynArrayDelete) {
  DynArray arr;
  arr.Push(10);
  arr.Push(20);
  arr.Delete();
  EXPECT_EQ(arr.Size(), 0u);
}

}  // namespace
