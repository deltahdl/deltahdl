// Non-LRM tests

#include <gtest/gtest.h>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulator/clocking.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(Clocking, FindNonexistent) {
  ClockingManager mgr;
  EXPECT_EQ(mgr.Find("nonexistent"), nullptr);
}

}  // namespace
