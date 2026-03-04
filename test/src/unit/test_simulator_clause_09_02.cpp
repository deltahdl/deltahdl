#include <gtest/gtest.h>

#include "simulator/process.h"

using namespace delta;

SimCoroutine MakeTestCoroutine() { co_return; }

namespace {

TEST(Process, ProcessKindEnum) {

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

}
