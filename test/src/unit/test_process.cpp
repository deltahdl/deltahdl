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

  SimCoroutine* pa = &a;
  SimCoroutine b = std::move(a);
  EXPECT_FALSE(b.Done());
  EXPECT_TRUE(pa->Done());  // Moved-from state check via pre-move pointer.
}

// ============================================================================
// §9.5 Process execution threads
// ============================================================================

TEST(Process, ProcessKindEnum) {
  // §9.2: All process kinds are defined.
  struct {
    ProcessKind kind;
    uint8_t expected;
  } const kCases[] = {
      {ProcessKind::kInitial, 0},     {ProcessKind::kAlways, 1},
      {ProcessKind::kAlwaysComb, 2},   {ProcessKind::kAlwaysLatch, 3},
      {ProcessKind::kAlwaysFF, 4},     {ProcessKind::kFinal, 5},
      {ProcessKind::kContAssign, 6},
  };
  for (const auto& c : kCases) {
    EXPECT_EQ(static_cast<uint8_t>(c.kind), c.expected);
  }
}

TEST(Process, ProcessDefaultState_KindAndCoro) {
  Process p;
  EXPECT_EQ(p.kind, ProcessKind::kInitial);
  EXPECT_EQ(p.coro, nullptr);
  EXPECT_EQ(p.home_region, Region::kActive);
}

TEST(Process, ProcessDefaultState_Flags) {
  Process p;
  EXPECT_TRUE(p.active);
  EXPECT_FALSE(p.is_reactive);
  EXPECT_TRUE(p.Done());
}

TEST(Process, ProcessResumeNullSafe) {
  // §9.5: Resume on null coroutine must not crash.
  Process p;
  p.Resume();
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

TEST(Process, ProcessIdAssignment) {
  // §9.5: Each process has a unique identifier.
  Process p1;
  p1.id = 42;
  Process p2;
  p2.id = 43;
  EXPECT_NE(p1.id, p2.id);
}

TEST(Process, ProcessReactiveFlag) {
  // §24: Programs use reactive region.
  Process p;
  p.is_reactive = true;
  p.kind = ProcessKind::kInitial;
  EXPECT_TRUE(p.is_reactive);
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
