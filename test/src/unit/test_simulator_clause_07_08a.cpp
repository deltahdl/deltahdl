// §7.8: Associative arrays

#include "common/arena.h"
#include "common/types.h"
#include "simulation/adv_sim.h"
#include <cstdint>
#include <gtest/gtest.h>
#include <string>

using namespace delta;

namespace {

// =============================================================================
// AssocArray
// =============================================================================
TEST(AdvSim, AssocArrayInsertAndLookup) {
  AssocArray arr;
  arr.Insert("key1", 100);
  arr.Insert("key2", 200);
  EXPECT_EQ(arr.Size(), 2u);
  EXPECT_EQ(arr.Lookup("key1"), 100u);
  EXPECT_EQ(arr.Lookup("key2"), 200u);
}

TEST(AdvSim, AssocArrayExistsAndErase) {
  AssocArray arr;
  arr.Insert("k", 1);
  EXPECT_TRUE(arr.Exists("k"));
  EXPECT_FALSE(arr.Exists("other"));
  arr.Erase("k");
  EXPECT_FALSE(arr.Exists("k"));
  EXPECT_EQ(arr.Size(), 0u);
}

} // namespace
