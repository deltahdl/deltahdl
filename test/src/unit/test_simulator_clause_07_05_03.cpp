#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/adv_sim.h"

using namespace delta;

namespace {

TEST(AdvSim, DynArrayDelete) {
  DynArray arr;
  arr.Push(10);
  arr.Push(20);
  arr.Delete();
  EXPECT_EQ(arr.Size(), 0u);
}

}
