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

struct ScannedSlot {
  uint64_t ticks;
  int type;
};

struct QueueReading {
  bool iterated = false;
  bool iterator_is_null = false;
  uint64_t now = 0;
  std::vector<ScannedSlot> slots;
};

QueueReading g_reading;

void ReadTheQueue() {
  s_vpi_time now = {};
  now.type = vpiSimTime;
  vpi_get_time(nullptr, &now);
  g_reading = {};
  g_reading.iterated = true;
  g_reading.now = TicksOf(now);
  vpiHandle it = vpi_iterate(vpiTimeQueue, nullptr);
  g_reading.iterator_is_null = it == nullptr;
  while (vpiHandle slot = it == nullptr ? nullptr : vpi_scan(it)) {
    s_vpi_time time = {};
    time.type = vpiSimTime;
    vpi_get_time(slot, &time);
    g_reading.slots.push_back({TicksOf(time), vpi_get(vpiType, slot)});
  }
}

PLI_INT32 ReadTheQueueCalltf(PLI_BYTE8*) {
  ReadTheQueue();
  return 0;
}

PLI_INT32 ReadTheQueueCallback(p_cb_data) {
  ReadTheQueue();
  return 0;
}

PLI_INT32 ReadTheQueueAtReadOnlySynchCalltf(PLI_BYTE8*) {
  s_vpi_time delay = {};
  delay.type = vpiSimTime;
  s_cb_data cb = {};
  cb.reason = cbReadOnlySynch;
  cb.time = &delay;
  cb.cb_rtn = &ReadTheQueueCallback;
  vpi_register_cb(&cb);
  return 0;
}

class TimeQueueReadInARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    g_reading = {};
    Register("$readq", &ReadTheQueueCalltf);
    Register("$readq_ros", &ReadTheQueueAtReadOnlySynchCalltf);
  }

  static void Register(const char* name, PLI_INT32 (*calltf)(PLI_BYTE8*)) {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText(name);
    data.calltf = calltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  static std::vector<uint64_t> TimesRead() {
    std::vector<uint64_t> times;
    times.reserve(g_reading.slots.size());
    for (const ScannedSlot& slot : g_reading.slots) times.push_back(slot.ticks);
    return times;
  }
};

TEST_F(TimeQueueReadInARun, EachScannedObjectIsATimeQueueInIncreasingTime) {
  Run("module top; logic x;\n"
      "  initial #30 x = 1;\n"
      "  initial #10 x = 0;\n"
      "  initial #20 x = 1;\n"
      "  initial #5 $readq;\n"
      "endmodule\n");
  ASSERT_TRUE(g_reading.iterated);
  ASSERT_EQ(TimesRead(), (std::vector<uint64_t>{10, 20, 30}));
  for (const ScannedSlot& slot : g_reading.slots) {
    EXPECT_EQ(slot.type, vpiTimeQueue);
  }
}

TEST_F(TimeQueueReadInARun, TheCurrentSlotIsReturnedWhileEventsPrecedeIt) {
  Run("module top; logic x;\n"
      "  initial begin #5 x <= 1; $readq; end\n"
      "  initial #20 x = 0;\n"
      "endmodule\n");
  ASSERT_TRUE(g_reading.iterated);
  EXPECT_EQ(g_reading.now, 5u);
  EXPECT_EQ(TimesRead(), (std::vector<uint64_t>{5, 20}));
}

TEST_F(TimeQueueReadInARun, TheCurrentSlotIsLeftOutAtReadOnlySynch) {
  Run("module top; logic x;\n"
      "  initial begin #5 x <= 1; $readq_ros; end\n"
      "  initial #20 x = 0;\n"
      "endmodule\n");
  ASSERT_TRUE(g_reading.iterated);
  EXPECT_EQ(g_reading.now, 5u);
  EXPECT_EQ(TimesRead(), (std::vector<uint64_t>{20}));
}

TEST_F(TimeQueueReadInARun, TheCurrentSlotIsLeftOutWhenNothingPrecedesIt) {
  Run("module top; logic x;\n"
      "  initial #5 $readq;\n"
      "  initial #20 x = 0;\n"
      "endmodule\n");
  ASSERT_TRUE(g_reading.iterated);
  EXPECT_EQ(TimesRead(), (std::vector<uint64_t>{20}));
}

TEST_F(TimeQueueReadInARun, NothingLeftInTheQueueGivesANullIterator) {
  Run("module top; logic x;\n"
      "  initial #5 $readq;\n"
      "endmodule\n");
  ASSERT_TRUE(g_reading.iterated);
  EXPECT_TRUE(g_reading.iterator_is_null);
}

TEST_F(TimeQueueReadInARun, OnlyTheCurrentSlotAtReadOnlySynchGivesANull) {
  Run("module top; logic x;\n"
      "  initial begin #5 x <= 1; $readq_ros; end\n"
      "endmodule\n");
  ASSERT_TRUE(g_reading.iterated);
  EXPECT_EQ(g_reading.now, 5u);
  EXPECT_TRUE(g_reading.iterator_is_null);
}

TEST_F(TimeQueueReadInARun, ADrainedSchedulerAtTheEndGivesANullIterator) {
  Run("module top; logic x;\n"
      "  initial begin x = 0; #5 x = 1; end\n"
      "  final $readq;\n"
      "endmodule\n");
  f_.scheduler.EndSimulation();
  ASSERT_TRUE(g_reading.iterated);
  EXPECT_TRUE(g_reading.iterator_is_null);
}

}  // namespace
}  // namespace delta
