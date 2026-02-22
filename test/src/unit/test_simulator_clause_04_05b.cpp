// §4.5: SystemVerilog simulation reference algorithm

#include <gtest/gtest.h>

#include "simulation/process.h"

using namespace delta;

// A real coroutine that produces a SimCoroutine.
SimCoroutine MakeTestCoroutine() { co_return; }

namespace {

TEST(Process, ProcessDefaultState_KindAndCoro) {
  Process p;
  EXPECT_EQ(p.kind, ProcessKind::kInitial);
  EXPECT_EQ(p.coro, nullptr);
  EXPECT_EQ(p.home_region, Region::kActive);
}

}  // namespace
