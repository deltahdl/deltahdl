#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.81 Time queue: the object model diagram for the simulation time queue. A
// circle reaches a "time queue" object, whose own time and vpi_get_time() come
// from §38.13. The clause carries no BNF and no 'shall' BNF productions, only
// three numbered details that govern the vpi_iterate(vpiTimeQueue, NULL) walk:
//   1) the time queue objects are returned in increasing order of simulation
//      time;
//   2) vpi_iterate() returns NULL when nothing is left in the queue;
//   3) the slot at the current simulation time is part of the iteration only
//      when there are events that precede read-only sync.
// These tests drive the production walk through the public vpi_iterate /
// vpi_scan dispatch after seeding the context's time queue.

// The fixture installs a context so the public vpi_iterate entry point runs its
// real dispatch over the seeded time queue.
class TimeQueue : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Detail 1: the iteration hands back the time queue objects in increasing order
// of simulation time, regardless of the order the slots were recorded in. Three
// future slots are seeded out of order; scanning the iterator yields them
// sorted by their recorded simulation time.
TEST_F(TimeQueue, ObjectsAreReturnedInIncreasingTimeOrder) {
  ctx_.SetTimeQueueSlots(
      {{30, false, false}, {10, false, false}, {20, false, false}});

  vpiHandle it = vpi_iterate(vpiTimeQueue, nullptr);
  ASSERT_NE(it, nullptr);

  vpiHandle a = vpi_scan(it);
  vpiHandle b = vpi_scan(it);
  vpiHandle c = vpi_scan(it);
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  ASSERT_NE(c, nullptr);

  EXPECT_EQ(VpiObjectOf(a)->type, vpiTimeQueue);
  EXPECT_EQ(VpiObjectOf(a)->time_queue_time, 10u);
  EXPECT_EQ(VpiObjectOf(b)->time_queue_time, 20u);
  EXPECT_EQ(VpiObjectOf(c)->time_queue_time, 30u);

  // The queue holds exactly three slots, so the next scan retires the iterator.
  EXPECT_EQ(vpi_scan(it), nullptr);
}

// Detail 2: when nothing is left in the simulation time queue, vpi_iterate()
// returns NULL rather than an iterator that immediately scans empty.
TEST_F(TimeQueue, EmptyQueueIteratesToNull) {
  ctx_.SetTimeQueueSlots({});

  EXPECT_EQ(vpi_iterate(vpiTimeQueue, nullptr), nullptr);
}

// Detail 3: the current-time slot takes part only when events remain before its
// read-only synch region. Here events do remain, so the slot yields a time
// queue object carrying its time; the exclusion case (events absent) is
// observed by FutureSlotContributesWhileCurrentSlotIsFiltered below.
TEST_F(TimeQueue, CurrentSlotIsIncludedWithEventsBeforeReadOnlySync) {
  ctx_.SetTimeQueueSlots({{5, true, true}});

  vpiHandle it = vpi_iterate(vpiTimeQueue, nullptr);
  ASSERT_NE(it, nullptr);

  vpiHandle slot = vpi_scan(it);
  ASSERT_NE(slot, nullptr);
  EXPECT_EQ(VpiObjectOf(slot)->type, vpiTimeQueue);
  EXPECT_EQ(VpiObjectOf(slot)->time_queue_time, 5u);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

// Detail 3 boundary: the read-only-sync condition gates only the current slot.
// A future slot always contributes even though its read-only flag is clear, so
// a future slot recorded alongside an excluded current slot still appears - and
// the surviving objects keep increasing-time order (detail 1). The current slot
// at time 5 is dropped; the future slot at time 8 remains.
TEST_F(TimeQueue, FutureSlotContributesWhileCurrentSlotIsFiltered) {
  ctx_.SetTimeQueueSlots({{5, true, false}, {8, false, false}});

  vpiHandle it = vpi_iterate(vpiTimeQueue, nullptr);
  ASSERT_NE(it, nullptr);

  vpiHandle only = vpi_scan(it);
  ASSERT_NE(only, nullptr);
  EXPECT_EQ(VpiObjectOf(only)->time_queue_time, 8u);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

// The times of the time queue objects the last call of $tq found after its
// own time, in the order the iteration handed them back.
std::vector<uint64_t> g_queued_times;

uint64_t TicksOf(const s_vpi_time& time) {
  return (static_cast<uint64_t>(time.high) << 32) | time.low;
}

PLI_INT32 TimeQueueCalltf(PLI_BYTE8* /*user_data*/) {
  s_vpi_time now = {};
  now.type = vpiSimTime;
  vpi_get_time(nullptr, &now);
  g_queued_times.clear();
  vpiHandle it = vpi_iterate(vpiTimeQueue, nullptr);
  while (vpiHandle slot = it == nullptr ? nullptr : vpi_scan(it)) {
    s_vpi_time time = {};
    time.type = vpiSimTime;
    vpi_get_time(slot, &time);
    if (TicksOf(time) > TicksOf(now)) g_queued_times.push_back(TicksOf(time));
  }
  return 0;
}

// A design run with the system task $tq registered beside the fixture's own,
// which reads the time queue from inside the run.
class TimeQueueOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    g_queued_times.clear();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$tq");
    data.calltf = &TimeQueueCalltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }
};

// A run's time queue is the time slots still holding events when it is read:
// a call at time 5 finds the slots of the delays still pending, at 10 and 30,
// in increasing time (detail 1).
TEST_F(TimeQueueOfARun, ARunsPendingSlotsAreItsTimeQueue) {
  Run("module top; logic x;\n"
      "  initial #30 x = 1;\n"
      "  initial #10 x = 0;\n"
      "  initial #5 $tq;\n"
      "endmodule\n");
  ASSERT_EQ(g_queued_times.size(), 2u);
  EXPECT_LT(g_queued_times[0], g_queued_times[1]);
}

}  // namespace
}  // namespace delta
