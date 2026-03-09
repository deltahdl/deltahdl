#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/adv_sim.h"

using namespace delta;

namespace {

TEST(AdvSim, AssocArrayInsertAndLookup) {
  AssocArray arr;
  arr.Insert("key1", 100);
  arr.Insert("key2", 200);
  EXPECT_EQ(arr.Size(), 2u);
  EXPECT_EQ(arr.Lookup("key1"), 100u);
  EXPECT_EQ(arr.Lookup("key2"), 200u);
}

}
