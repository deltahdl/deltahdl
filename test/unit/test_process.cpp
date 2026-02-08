#include <gtest/gtest.h>

#include "simulation/process.h"

using namespace delta;

namespace {

// A real coroutine that produces a SimCoroutine.
SimCoroutine MakeTestCoroutine() { co_return; }

}  // namespace

TEST(Process, CoroutineLifecycle) {
  SimCoroutine coro = MakeTestCoroutine();
  EXPECT_FALSE(coro.Done());

  coro.Resume();
  EXPECT_TRUE(coro.Done());
}

TEST(Process, MoveSemantics) {
  SimCoroutine a = MakeTestCoroutine();
  EXPECT_FALSE(a.Done());

  SimCoroutine b = std::move(a);
  EXPECT_FALSE(b.Done());
  EXPECT_TRUE(a.Done());  // NOLINT -- moved-from state check
}
