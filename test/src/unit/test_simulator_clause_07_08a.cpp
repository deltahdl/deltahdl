// Non-LRM tests

#include <gtest/gtest.h>
#include <cstdint>
#include <string>
#include "common/arena.h"
#include "common/types.h"
#include "simulator/adv_sim.h"

using namespace delta;

namespace {

TEST(AdvSim, AssocArrayExistsAndErase) {
  AssocArray arr;
  arr.Insert("k", 1);
  EXPECT_TRUE(arr.Exists("k"));
  EXPECT_FALSE(arr.Exists("other"));
  arr.Erase("k");
  EXPECT_FALSE(arr.Exists("k"));
  EXPECT_EQ(arr.Size(), 0u);
}

}  // namespace
