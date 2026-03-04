// §7.5.2: Size()

#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/adv_sim.h"

using namespace delta;

namespace {

// =============================================================================
// DynArray
// =============================================================================
TEST(AdvSim, DynArrayDefaultEmpty) {
  DynArray arr;
  EXPECT_EQ(arr.Size(), 0u);
}

}  // namespace
