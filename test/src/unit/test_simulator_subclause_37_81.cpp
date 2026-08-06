#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

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

  EXPECT_EQ(a->type, vpiTimeQueue);
  EXPECT_EQ(a->time_queue_time, 10u);
  EXPECT_EQ(b->time_queue_time, 20u);
  EXPECT_EQ(c->time_queue_time, 30u);

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
  EXPECT_EQ(slot->type, vpiTimeQueue);
  EXPECT_EQ(slot->time_queue_time, 5u);
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
  EXPECT_EQ(only->time_queue_time, 8u);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

}  // namespace
}  // namespace delta
