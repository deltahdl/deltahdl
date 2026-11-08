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

class TimeQueue : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

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

  EXPECT_EQ(vpi_scan(it), nullptr);
}

TEST_F(TimeQueue, EmptyQueueIteratesToNull) {
  ctx_.SetTimeQueueSlots({});

  EXPECT_EQ(vpi_iterate(vpiTimeQueue, nullptr), nullptr);
}

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

TEST_F(TimeQueue, FutureSlotContributesWhileCurrentSlotIsFiltered) {
  ctx_.SetTimeQueueSlots({{5, true, false}, {8, false, false}});

  vpiHandle it = vpi_iterate(vpiTimeQueue, nullptr);
  ASSERT_NE(it, nullptr);

  vpiHandle only = vpi_scan(it);
  ASSERT_NE(only, nullptr);
  EXPECT_EQ(VpiObjectOf(only)->time_queue_time, 8u);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

std::vector<uint64_t> g_queued_times;

uint64_t TicksOf(const s_vpi_time& time) {
  return (static_cast<uint64_t>(time.high) << 32) | time.low;
}

PLI_INT32 TimeQueueCalltf(PLI_BYTE8*) {
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
