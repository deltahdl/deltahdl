#include <gtest/gtest.h>

#include "simulator/process.h"

using namespace delta;

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
  auto coro = MakeTestCoroutine();
  Process p;
  p.coro = coro.Release();
  EXPECT_FALSE(p.Done());
  p.Resume();
  EXPECT_TRUE(p.Done());
}

}  // namespace
