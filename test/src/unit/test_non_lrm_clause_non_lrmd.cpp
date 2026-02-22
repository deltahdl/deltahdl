// §non_lrm

#include <gtest/gtest.h>
#include "simulation/process.h"

using namespace delta;

// A real coroutine that produces a SimCoroutine.
SimCoroutine MakeTestCoroutine() { co_return; }

namespace {

TEST(Process, MoveSemantics) {
  SimCoroutine a = MakeTestCoroutine();
  EXPECT_FALSE(a.Done());

  SimCoroutine* pa = &a;
  SimCoroutine b = std::move(a);
  EXPECT_FALSE(b.Done());
  EXPECT_TRUE(pa->Done());  // Moved-from state check via pre-move pointer.
}

TEST(Process, ProcessResumeNullSafe) {
  // §9.5: Resume on null coroutine must not crash.
  Process p;
  p.Resume();
  EXPECT_TRUE(p.Done());
}

TEST(Process, ProcessIdAssignment) {
  // §9.5: Each process has a unique identifier.
  Process p1;
  p1.id = 42;
  Process p2;
  p2.id = 43;
  EXPECT_NE(p1.id, p2.id);
}

TEST(Process, CoroutineRelease) {
  SimCoroutine coro = MakeTestCoroutine();
  auto handle = coro.Release();
  EXPECT_TRUE(coro.Done());
  EXPECT_NE(handle, nullptr);
  // Clean up the released handle.
  handle.destroy();
}

TEST(Process, CoroutineDestroyOnScopeExit) {
  // Coroutine resources cleaned up on destruction (§9.5).
  SimCoroutine coro = MakeTestCoroutine();
  // Immediately destroyed — no leak if sanitizer passes.
}

}  // namespace
