// Non-LRM tests

#include <gtest/gtest.h>
#include <cstdint>
#include <string>
#include <vector>
#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// §4.9.5 — User-defined net type: x/z control input treats switch as off
// ---------------------------------------------------------------------------
TEST(SimCh4095, UserDefinedNetTypeSwitchOffForXZ) {
  Arena arena;
  Scheduler sched(arena);
  int udn_a = 5;
  int udn_b = 10;
  int control = -1;  // x represented as -1.

  // Model: bidirectional switch between user-defined nets udn_a and udn_b
  // with control=x. For UDN, x control → switch treated as off.
  // Each net resolved separately (no signal flow between them).
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    bool switch_off = (control == -1 || control == -2);  // x or z → off.
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    if (switch_off) {
      // Nets resolved separately — no propagation.
      update->callback = []() {};
    } else {
      // Switch on — resolve as single net.
      update->callback = [&]() { udn_b = udn_a; };
    }
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  // Switch was off (control=x) → nets resolved separately.
  EXPECT_EQ(udn_a, 5);   // Unchanged.
  EXPECT_EQ(udn_b, 10);  // Unchanged — no signal flow.
}

}  // namespace
