// §9.5: Process execution threads

#include <gtest/gtest.h>

#include "simulation/process.h"

using namespace delta;

// A real coroutine that produces a SimCoroutine.
SimCoroutine MakeTestCoroutine() { co_return; }

namespace {

TEST(Process, CoroutineLifecycle) {
  SimCoroutine coro = MakeTestCoroutine();
  EXPECT_FALSE(coro.Done());

  coro.Resume();
  EXPECT_TRUE(coro.Done());
}

TEST(Process, ProcessDefaultState_Flags) {
  Process p;
  EXPECT_TRUE(p.active);
  EXPECT_FALSE(p.is_reactive);
  EXPECT_TRUE(p.Done());
}

TEST(Process, ProcessWithCoroutine) {
  // §9.5: Process can hold and execute a coroutine.
  auto coro = MakeTestCoroutine();
  Process p;
  p.coro = coro.Release();
  EXPECT_FALSE(p.Done());
  p.Resume();
  EXPECT_TRUE(p.Done());
}

}  // namespace
