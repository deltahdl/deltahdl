#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_vpi_run.h"
#include "simulator/scheduler.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiGetTimeSim : public ::testing::Test {
 protected:
  void SetUp() override {
    vpi_ctx_.SetScheduler(&scheduler_);
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  void AdvanceTo(uint64_t t) {
    auto* ev = scheduler_.GetEventPool().Acquire();
    ev->callback = []() {};
    scheduler_.ScheduleEvent(SimTime{t}, Region::kActive, ev);
    scheduler_.Run();
  }

  void SchedulePendingAt(uint64_t t) {
    auto* ev = scheduler_.GetEventPool().Acquire();
    ev->callback = []() {};
    scheduler_.ScheduleEvent(SimTime{t}, Region::kActive, ev);
  }

  Arena arena_;
  Scheduler scheduler_{arena_};
  VpiContext vpi_ctx_;
};

TEST_F(VpiGetTimeSim, SimTimeSplitsAcrossHighAndLow) {
  const uint64_t kTicks = (static_cast<uint64_t>(3) << 32) | 5u;
  AdvanceTo(kTicks);

  s_vpi_time out = {};
  out.type = vpiSimTime;
  vpi_get_time(nullptr, &out);

  EXPECT_EQ(out.high, 3u);
  EXPECT_EQ(out.low, 5u);
}

TEST_F(VpiGetTimeSim, TypeFieldSelectsSimVersusScaledReal) {
  AdvanceTo(7);

  s_vpi_time as_sim = {};
  as_sim.type = vpiSimTime;
  vpi_get_time(nullptr, &as_sim);
  EXPECT_EQ(as_sim.low, 7u);
  EXPECT_DOUBLE_EQ(as_sim.real, 0.0);

  s_vpi_time as_real = {};
  as_real.type = vpiScaledRealTime;
  vpi_get_time(nullptr, &as_real);
  EXPECT_DOUBLE_EQ(as_real.real, 7.0);
  EXPECT_EQ(as_real.low, 0u);
}

TEST_F(VpiGetTimeSim, ScaledRealUsesObjectTimescale) {
  vpi_ctx_.SetSimTimeUnit(-12);
  AdvanceTo(1000);

  VpiHandle obj = vpi_ctx_.CreateModule("top", "top");
  ASSERT_NE(obj, nullptr);
  obj->time_unit = -9;

  s_vpi_time out = {};
  out.type = vpiScaledRealTime;
  vpi_get_time(VpiHandleOf(obj), &out);

  EXPECT_DOUBLE_EQ(out.real, 1.0);
}

TEST_F(VpiGetTimeSim, NullObjectUsesSimulationTimeUnit) {
  vpi_ctx_.SetSimTimeUnit(-12);
  AdvanceTo(1000);

  s_vpi_time out = {};
  out.type = vpiScaledRealTime;
  vpi_get_time(nullptr, &out);

  EXPECT_DOUBLE_EQ(out.real, 1000.0);
}

TEST_F(VpiGetTimeSim, TimeQueueReportsNextFutureEvent) {
  SchedulePendingAt(50);

  s_vpi_time now = {};
  now.type = vpiSimTime;
  vpi_get_time(nullptr, &now);
  EXPECT_EQ(now.low, 0u);

  VpiHandle tq = vpi_ctx_.CreateTimeQueue();
  ASSERT_NE(tq, nullptr);

  s_vpi_time future = {};
  future.type = vpiSimTime;
  vpi_get_time(VpiHandleOf(tq), &future);
  EXPECT_EQ(future.low, 50u);
}

TEST_F(VpiGetTimeSim, ATimeQueueWithNoSchedulerReadsZero) {
  VpiContext bare;
  SetGlobalVpiContext(&bare);
  VpiHandle tq = bare.CreateTimeQueue();
  s_vpi_time future = {};
  future.type = vpiSimTime;
  future.low = 9;
  vpi_get_time(VpiHandleOf(tq), &future);
  SetGlobalVpiContext(&vpi_ctx_);
  EXPECT_EQ(future.low, 0u);
}

TEST_F(VpiGetTimeSim, TimeQueueUsesSimulationTimeUnit) {
  vpi_ctx_.SetSimTimeUnit(-12);
  SchedulePendingAt(1000);

  VpiHandle tq = vpi_ctx_.CreateTimeQueue();
  ASSERT_NE(tq, nullptr);

  s_vpi_time out = {};
  out.type = vpiScaledRealTime;
  vpi_get_time(VpiHandleOf(tq), &out);

  EXPECT_DOUBLE_EQ(out.real, 1000.0);
}

TEST_F(VpiGetTimeSim, IteratedSlotsReportTheirOwnScheduledTime) {
  SchedulePendingAt(50);
  vpi_ctx_.SetTimeQueueSlots({{40, false, false}, {10, false, false}});

  vpiHandle it = vpi_iterate(vpiTimeQueue, nullptr);
  ASSERT_NE(it, nullptr);

  vpiHandle first = vpi_scan(it);
  vpiHandle second = vpi_scan(it);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);

  s_vpi_time t0 = {};
  t0.type = vpiSimTime;
  vpi_get_time(first, &t0);
  EXPECT_EQ(t0.low, 10u);

  s_vpi_time t1 = {};
  t1.type = vpiSimTime;
  vpi_get_time(second, &t1);
  EXPECT_EQ(t1.low, 40u);
}

TEST_F(VpiGetTimeSim, WritesIntoApplicationAllocatedMemory) {
  AdvanceTo(9);

  s_vpi_time caller_owned = {};
  caller_owned.type = vpiSimTime;
  s_vpi_time* before = &caller_owned;
  vpi_get_time(nullptr, &caller_owned);

  EXPECT_EQ(before, &caller_owned);
  EXPECT_EQ(caller_owned.low, 9u);
}

TEST_F(VpiGetTimeSim, NullDestinationIsSafe) {
  AdvanceTo(3);
  vpi_get_time(nullptr, nullptr);
  SUCCEED();
}

struct ProbedTimes {
  uint32_t sim_low = 0;
  uint32_t sim_high = 0;
  double top_scaled = 0.0;
  double sub_scaled = 0.0;
};

ProbedTimes& ProbedTimesOfTheCall() {
  static ProbedTimes times;
  return times;
}

PLI_INT32 ReadTimesCalltf(PLI_BYTE8*) {
  ProbedTimes& times = ProbedTimesOfTheCall();
  s_vpi_time t = {};
  t.type = vpiSimTime;
  vpi_get_time(nullptr, &t);
  times.sim_low = t.low;
  times.sim_high = t.high;
  t.type = vpiScaledRealTime;
  vpi_get_time(vpi_handle_by_name(VpiText("top"), nullptr), &t);
  times.top_scaled = t.real;
  vpi_get_time(vpi_handle_by_name(VpiText("top.s"), nullptr), &t);
  times.sub_scaled = t.real;
  return 0;
}

class TimesOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    ProbedTimesOfTheCall() = ProbedTimes{};
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$probe");
    data.calltf = &ReadTimesCalltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
    Run("module sub; timeunit 1ps; timeprecision 1ps; endmodule\n"
        "module top; timeunit 1ns; timeprecision 1ps;\n"
        "  sub s();\n"
        "  initial #7 $probe;\n"
        "endmodule\n");
  }
};

TEST_F(TimesOfARun, ANullObjectReadsTheRunsTimeInTheSimulationUnit) {
  EXPECT_EQ(ProbedTimesOfTheCall().sim_low, 7000u);
  EXPECT_EQ(ProbedTimesOfTheCall().sim_high, 0u);
}

TEST_F(TimesOfARun, AnObjectReadsTheRunsTimeInItsOwnUnit) {
  EXPECT_DOUBLE_EQ(ProbedTimesOfTheCall().top_scaled, 7.0);
  EXPECT_DOUBLE_EQ(ProbedTimesOfTheCall().sub_scaled, 7000.0);
}

double scaled_net_time = 0.0;
double callback_scaled_time = 0.0;

vpiHandle TopS() { return vpi_handle_by_name(VpiText("top.s"), nullptr); }

double ScaledTimeOfTopS() {
  s_vpi_time time = {};
  time.type = vpiScaledRealTime;
  vpi_get_time(TopS(), &time);
  return time.real;
}

PLI_INT32 AfterDelayCallback(p_cb_data) {
  callback_scaled_time = ScaledTimeOfTopS();
  return 0;
}

PLI_INT32 ScaledCalltf(PLI_BYTE8*) {
  scaled_net_time = ScaledTimeOfTopS();
  s_vpi_value value = {};
  value.format = vpiScalarVal;
  value.value.scalar = vpi1;
  s_vpi_time delay = {};
  delay.type = vpiScaledRealTime;
  delay.real = 2.0;
  vpi_put_value(TopS(), &value, &delay, vpiInertialDelay);
  s_vpi_time after = {};
  after.type = vpiScaledRealTime;
  after.real = 3.0;
  s_cb_data cb = {};
  cb.reason = cbAfterDelay;
  cb.cb_rtn = &AfterDelayCallback;
  cb.obj = TopS();
  cb.time = &after;
  vpi_register_cb(&cb);
  return 0;
}

class ScaledTimeOfAVariable : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    scaled_net_time = 0.0;
    callback_scaled_time = 0.0;
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$scaled");
    data.calltf = &ScaledCalltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
    Run("module top; timeunit 1ns; timeprecision 1ps;\n"
        "  logic s = 0; realtime changed_at = 0;\n"
        "  always @(s) changed_at = $realtime;\n"
        "  initial #7 $scaled;\n"
        "endmodule\n");
  }
};

TEST_F(ScaledTimeOfAVariable, ItsTimeIsReadInItsModulesUnit) {
  EXPECT_DOUBLE_EQ(scaled_net_time, 7.0);
}

TEST_F(ScaledTimeOfAVariable, APutDelayIsInItsModulesUnit) {
  s_vpi_value value = {};
  value.format = vpiRealVal;
  vpi_get_value(By("top.changed_at"), &value);
  EXPECT_DOUBLE_EQ(value.value.real, 9.0);
}

TEST_F(ScaledTimeOfAVariable, AnAfterDelayCallbackIsInItsModulesUnit) {
  EXPECT_DOUBLE_EQ(callback_scaled_time, 10.0);
}

}  // namespace
}  // namespace delta
