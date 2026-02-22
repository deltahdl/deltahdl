// §9.2: Structured procedures

#include <gtest/gtest.h>
#include "simulation/process.h"

using namespace delta;

// A real coroutine that produces a SimCoroutine.
SimCoroutine MakeTestCoroutine() { co_return; }

namespace {

// ============================================================================
// §9.5 Process execution threads
// ============================================================================
TEST(Process, ProcessKindEnum) {
  // §9.2: All process kinds are defined.
  struct {
    ProcessKind kind;
    uint8_t expected;
  } const kCases[] = {
      {ProcessKind::kInitial, 0},    {ProcessKind::kAlways, 1},
      {ProcessKind::kAlwaysComb, 2}, {ProcessKind::kAlwaysLatch, 3},
      {ProcessKind::kAlwaysFF, 4},   {ProcessKind::kFinal, 5},
      {ProcessKind::kContAssign, 6},
  };
  for (const auto& c : kCases) {
    EXPECT_EQ(static_cast<uint8_t>(c.kind), c.expected);
  }
}

}  // namespace
