// §24

#include "simulation/process.h"
#include <gtest/gtest.h>

using namespace delta;

// A real coroutine that produces a SimCoroutine.
SimCoroutine MakeTestCoroutine() { co_return; }

namespace {

TEST(Process, ProcessReactiveFlag) {
  // §24: Programs use reactive region.
  Process p;
  p.is_reactive = true;
  p.kind = ProcessKind::kInitial;
  EXPECT_TRUE(p.is_reactive);
}

} // namespace
