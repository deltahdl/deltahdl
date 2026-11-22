#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_vpi_run.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

const int kSimTimeReasons[] = {
    cbAtStartOfSimTime, cbNBASynch,    cbReadWriteSynch, cbAtEndOfSimTime,
    cbReadOnlySynch,    cbNextSimTime, cbAfterDelay,
};

bool g_inner_called = false;
vpiHandle g_inner_handle = nullptr;
int RegisterZeroDelayWithinCallback(s_cb_data*) {
  g_inner_called = true;
  static s_vpi_time t = {};
  t.type = vpiSimTime;
  s_cb_data inner = {};
  inner.reason = cbAtStartOfSimTime;
  inner.time = &t;
  g_inner_handle = vpi_register_cb(&inner);
  return 0;
}

struct DeliveredCbData {
  const s_cb_data* structure = nullptr;
  bool had_time = false;
  int time_type = 0;
  uint32_t time_low = 0;
  uint32_t time_high = 0;
  double time_real = 0.0;
  bool had_value = false;
  void* user_data = nullptr;
};
DeliveredCbData g_delivered;
int RecordDelivery(s_cb_data* data) {
  g_delivered.structure = data;
  g_delivered.had_time = data->time != nullptr;
  if (data->time != nullptr) {
    g_delivered.time_type = data->time->type;
    g_delivered.time_low = data->time->low;
    g_delivered.time_high = data->time->high;
    g_delivered.time_real = data->time->real;
  }
  g_delivered.had_value = data->value != nullptr;
  g_delivered.user_data = data->user_data;
  return 0;
}

class VpiSimTimeCallbacks : public ::testing::Test {
 protected:
  void SetUp() override {
    g_inner_called = false;
    g_inner_handle = nullptr;
    g_delivered = DeliveredCbData{};
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

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

TEST_F(VpiSimTimeCallbacks, AllSimTimeReasonsRegisterWithValidTime) {
  for (int reason : kSimTimeReasons) {
    s_vpi_time t = {};
    t.type = vpiSimTime;
    t.low = 1;
    s_cb_data cb = {};
    cb.reason = reason;
    cb.time = &t;
    vpiHandle h = vpi_register_cb(&cb);
    EXPECT_NE(h, nullptr) << "reason=" << reason;
    EXPECT_EQ(vpi_ctx_.RegisteredCallbacks().back().reason, reason);
  }
}

TEST_F(VpiSimTimeCallbacks, NullTimeStructureIsRejected) {
  s_cb_data cb = {};
  cb.reason = cbAtEndOfSimTime;
  cb.time = nullptr;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);
}

TEST_F(VpiSimTimeCallbacks, SuppressTimeTypeIsRejected) {
  s_vpi_time t = {};
  t.type = vpiSuppressTime;
  s_cb_data cb = {};
  cb.reason = cbNBASynch;
  cb.time = &t;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);
}

TEST_F(VpiSimTimeCallbacks, NonSimTimeReasonIgnoresTimeRequirement) {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  cb.time = nullptr;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

TEST_F(VpiSimTimeCallbacks, ZeroDelayAtStartOfSimTimeRejectedAfterTimeSlice) {
  vpi_ctx_.SetSimulationProgressedIntoTimeSlice(true);

  s_vpi_time t = {};
  t.type = vpiSimTime;
  s_cb_data cb = {};
  cb.reason = cbAtStartOfSimTime;
  cb.time = &t;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);
}

TEST_F(VpiSimTimeCallbacks, NonZeroDelayAtStartOfSimTimeAllowedAfterTimeSlice) {
  vpi_ctx_.SetSimulationProgressedIntoTimeSlice(true);

  s_vpi_time t = {};
  t.type = vpiSimTime;
  t.low = 1;
  s_cb_data cb = {};
  cb.reason = cbAtStartOfSimTime;
  cb.time = &t;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

TEST_F(VpiSimTimeCallbacks, ZeroDelayAtStartOfSimTimeAllowedBeforeTimeSlice) {
  s_vpi_time t = {};
  t.type = vpiSimTime;
  s_cb_data cb = {};
  cb.reason = cbAtStartOfSimTime;
  cb.time = &t;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

TEST_F(VpiSimTimeCallbacks, ZeroDelayAtStartOfSimTimeAllowedWithinCallback) {
  vpi_ctx_.SetSimulationProgressedIntoTimeSlice(true);

  s_vpi_time outer_t = {};
  outer_t.type = vpiSimTime;
  outer_t.low = 1;
  s_cb_data outer = {};
  outer.reason = cbAtStartOfSimTime;
  outer.cb_rtn = &RegisterZeroDelayWithinCallback;
  outer.time = &outer_t;
  vpiHandle outer_handle = vpi_register_cb(&outer);
  ASSERT_NE(outer_handle, nullptr);

  vpi_ctx_.DispatchCallbacks(cbAtStartOfSimTime);

  EXPECT_TRUE(g_inner_called);
  EXPECT_NE(g_inner_handle, nullptr);
}

TEST_F(VpiSimTimeCallbacks, ZeroDelayReadWriteSynchRejectedAtReadOnlySynch) {
  vpi_ctx_.SetAtReadOnlySynchTime(true);

  s_vpi_time t = {};
  t.type = vpiSimTime;
  s_cb_data cb = {};
  cb.reason = cbReadWriteSynch;
  cb.time = &t;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);
}

TEST_F(VpiSimTimeCallbacks, ZeroDelayReadWriteSynchAllowedWhenNotReadOnly) {
  s_vpi_time t = {};
  t.type = vpiSimTime;
  s_cb_data cb = {};
  cb.reason = cbReadWriteSynch;
  cb.time = &t;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

TEST_F(VpiSimTimeCallbacks, NonZeroDelayReadWriteSynchAllowedAtReadOnlySynch) {
  vpi_ctx_.SetAtReadOnlySynchTime(true);

  s_vpi_time t = {};
  t.type = vpiSimTime;
  t.low = 1;
  s_cb_data cb = {};
  cb.reason = cbReadWriteSynch;
  cb.time = &t;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

TEST_F(VpiSimTimeCallbacks, HighWordDelayCountsAsNonZeroForAtStartOfSimTime) {
  vpi_ctx_.SetSimulationProgressedIntoTimeSlice(true);

  s_vpi_time t = {};
  t.type = vpiSimTime;
  t.low = 0;
  t.high = 1;
  s_cb_data cb = {};
  cb.reason = cbAtStartOfSimTime;
  cb.time = &t;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

TEST_F(VpiSimTimeCallbacks, RealDelayCountsAsNonZeroForAtStartOfSimTime) {
  vpi_ctx_.SetSimulationProgressedIntoTimeSlice(true);

  s_vpi_time t = {};
  t.type = vpiScaledRealTime;
  t.low = 0;
  t.high = 0;
  t.real = 1.0;
  s_cb_data cb = {};
  cb.reason = cbAtStartOfSimTime;
  cb.time = &t;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

TEST_F(VpiSimTimeCallbacks, RoutineIsPassedTheCurrentTimeAndItsOwnStructure) {
  AdvanceTo(40);

  int user_object = 7;
  s_vpi_time requested = {};
  requested.type = vpiSimTime;
  requested.low = 5;
  s_cb_data cb = {};
  cb.reason = cbAfterDelay;
  cb.time = &requested;
  cb.cb_rtn = RecordDelivery;
  cb.user_data = reinterpret_cast<PLI_BYTE8*>(&user_object);
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbAfterDelay), 1);
  ASSERT_TRUE(g_delivered.had_time);
  EXPECT_EQ(g_delivered.time_type, vpiSimTime);
  EXPECT_EQ(g_delivered.time_low, 40u);
  EXPECT_EQ(g_delivered.time_high, 0u);
  EXPECT_EQ(g_delivered.user_data, reinterpret_cast<PLI_BYTE8*>(&user_object));

  EXPECT_NE(g_delivered.structure, &cb);
  EXPECT_EQ(requested.low, 5u);
}

TEST_F(VpiSimTimeCallbacks, EveryReasonDeliversTheCurrentTimeAndNoValue) {
  AdvanceTo(12);

  for (int reason : kSimTimeReasons) {
    if (reason == cbNextSimTime) continue;
    g_delivered = DeliveredCbData{};

    s_vpi_value value = {};
    value.format = vpiIntVal;
    s_vpi_time requested = {};
    requested.type = vpiSimTime;
    requested.low = 900;
    s_cb_data cb = {};
    cb.reason = reason;
    cb.time = &requested;
    cb.value = &value;
    cb.cb_rtn = RecordDelivery;
    ASSERT_NE(vpi_register_cb(&cb), nullptr) << "reason " << reason;

    EXPECT_EQ(vpi_ctx_.DispatchCallbacks(reason), 1) << "reason " << reason;
    EXPECT_TRUE(g_delivered.had_time) << "reason " << reason;
    EXPECT_EQ(g_delivered.time_low, 12u) << "reason " << reason;
    EXPECT_FALSE(g_delivered.had_value) << "reason " << reason;
  }
}

TEST_F(VpiSimTimeCallbacks, ScaledRealTimeIsScaledToTheObjFieldsTimeUnit) {
  vpi_ctx_.SetSimTimeUnit(-12);
  AdvanceTo(3000);

  VpiHandle scope = vpi_ctx_.CreateModule("m", "m");
  scope->time_unit = -9;

  s_vpi_time requested = {};
  requested.type = vpiScaledRealTime;
  requested.real = 1.0;
  s_cb_data cb = {};
  cb.reason = cbReadOnlySynch;
  cb.time = &requested;
  cb.obj = VpiHandleOf(scope);
  cb.cb_rtn = RecordDelivery;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbReadOnlySynch), 1);
  ASSERT_TRUE(g_delivered.had_time);
  EXPECT_EQ(g_delivered.time_type, vpiScaledRealTime);
  EXPECT_DOUBLE_EQ(g_delivered.time_real, 3.0);
}

TEST_F(VpiSimTimeCallbacks, NextSimTimeIgnoresTheTimeItWasRegisteredWith) {
  AdvanceTo(8);

  s_vpi_value value = {};
  value.format = vpiIntVal;
  s_vpi_time requested = {};
  requested.type = vpiSimTime;
  requested.low = 0xFFFFFFFFu;
  requested.high = 0xFFFFFFFFu;
  s_cb_data cb = {};
  cb.reason = cbNextSimTime;
  cb.time = &requested;
  cb.value = &value;
  cb.cb_rtn = RecordDelivery;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);
  ASSERT_FALSE(g_delivered.had_time);

  AdvanceTo(9);

  ASSERT_TRUE(g_delivered.had_time);
  EXPECT_EQ(g_delivered.time_low, 9u);
  EXPECT_EQ(g_delivered.time_high, 0u);
  EXPECT_FALSE(g_delivered.had_value);
}

TEST_F(VpiSimTimeCallbacks, ANonSimTimeReasonKeepsTheTimeItWasRegisteredWith) {
  AdvanceTo(25);

  s_vpi_value value = {};
  value.format = vpiIntVal;
  s_vpi_time requested = {};
  requested.type = vpiSimTime;
  requested.low = 900;
  s_cb_data cb = {};
  cb.reason = cbEndOfCompile;
  cb.time = &requested;
  cb.value = &value;
  cb.cb_rtn = RecordDelivery;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbEndOfCompile), 1);
  ASSERT_TRUE(g_delivered.had_time);
  EXPECT_EQ(g_delivered.time_low, 900u);
  EXPECT_TRUE(g_delivered.had_value);
}

struct TimeDelivery {
  std::string label;
  uint32_t time = 0;
  int value = 0;
  bool operator==(const TimeDelivery&) const = default;
};

std::vector<TimeDelivery>& TimeDeliveries() {
  static std::vector<TimeDelivery> deliveries;
  return deliveries;
}

int IntOfTop(const char* name) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(vpi_handle_by_name(VpiText(name), nullptr), &value);
  return value.value.integer;
}

PLI_INT32 RecordTimeDelivery(p_cb_data cb) {
  TimeDeliveries().push_back({cb->user_data,
                              cb->time != nullptr ? cb->time->low : 0,
                              IntOfTop("top.q")});
  return 0;
}

void PlaceTimeCallback(int reason, uint32_t delay, const char* label,
                       PLI_INT32 (*rtn)(p_cb_data) = &RecordTimeDelivery) {
  static s_vpi_time time;
  time.type = vpiSimTime;
  time.high = 0;
  time.low = delay;
  s_cb_data data = {};
  data.reason = reason;
  data.cb_rtn = rtn;
  data.time = &time;
  data.user_data = VpiText(label);
  vpi_register_cb(&data);
}

class TimeCallbacksOfARun : public VpiDesignRun {
 protected:
  void RunArmedBy(PLI_INT32 (*arm)(p_cb_data), const char* src) {
    TimeDeliveries().clear();
    s_cb_data data = {};
    data.reason = cbStartOfSimulation;
    data.cb_rtn = arm;
    ASSERT_NE(vpi_register_cb(&data), nullptr);
    Run(src);
  }
};

PLI_INT32 ArmEveryTimeReason(p_cb_data) {
  PlaceTimeCallback(cbAtStartOfSimTime, 5, "start-of-5");
  PlaceTimeCallback(cbNBASynch, 5, "nba-synch-5");
  PlaceTimeCallback(cbAtEndOfSimTime, 5, "end-of-5");
  PlaceTimeCallback(cbReadOnlySynch, 5, "read-only-5");
  PlaceTimeCallback(cbAfterDelay, 7, "after-delay-7");
  PlaceTimeCallback(cbNextSimTime, 0, "next-sim-time");
  return 0;
}

TEST_F(TimeCallbacksOfARun, EachTimeReasonIsCalledAtItsPointOfTheSlot) {
  RunArmedBy(&ArmEveryTimeReason,
             "module top; timeunit 1ns; timeprecision 1ns; int q;\n"
             "  initial begin #5; q <= 1; #5; end\n"
             "endmodule\n");
  EXPECT_EQ(TimeDeliveries(), (std::vector<TimeDelivery>{
                                  {"next-sim-time", 5, 0},
                                  {"start-of-5", 5, 0},
                                  {"nba-synch-5", 5, 0},
                                  {"end-of-5", 5, 1},
                                  {"read-only-5", 5, 1},
                                  {"after-delay-7", 7, 1},
                              }));
}

std::vector<bool>& PutRefusals() {
  static std::vector<bool> refusals;
  return refusals;
}

PLI_INT32 PutIntoQ(p_cb_data cb) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = cb->reason == cbReadWriteSynch ? 3 : 4;
  vpi_put_value(vpi_handle_by_name(VpiText("top.q"), nullptr), &value, nullptr,
                vpiNoDelay);
  PutRefusals().push_back(vpi_chk_error(nullptr) != 0);
  return 0;
}

PLI_INT32 ArmSynchWrites(p_cb_data) {
  PlaceTimeCallback(cbReadWriteSynch, 2, "rw", &PutIntoQ);
  PlaceTimeCallback(cbReadOnlySynch, 2, "ro", &PutIntoQ);
  return 0;
}

TEST_F(TimeCallbacksOfARun, APutFromReadOnlySynchIsRefused) {
  PutRefusals().clear();
  RunArmedBy(&ArmSynchWrites,
             "module top; timeunit 1ns; timeprecision 1ns; int q;\n"
             "  initial #3;\n"
             "endmodule\n");
  EXPECT_EQ(PutRefusals(), (std::vector<bool>{false, true}));
  EXPECT_EQ(IntOfTop("top.q"), 3);
}

void ExpectRefusedWithAMessage(vpiHandle placed) {
  EXPECT_EQ(placed, nullptr);
  s_vpi_error_info info = {};
  const PLI_INT32 kLevel = vpi_chk_error(&info);
  EXPECT_EQ(kLevel, vpiError);
  EXPECT_EQ(info.level, vpiError);
  ASSERT_NE(info.message, nullptr);
  EXPECT_FALSE(std::string(info.message).empty());
}

TEST_F(VpiSimTimeCallbacks, EveryTimeReasonRefusesANullTimeWithAMessage) {
  for (int reason : kSimTimeReasons) {
    SCOPED_TRACE(reason);
    s_cb_data cb = {};
    cb.reason = reason;
    cb.cb_rtn = RecordDelivery;
    ExpectRefusedWithAMessage(vpi_register_cb(&cb));
  }
}

TEST_F(VpiSimTimeCallbacks, EveryTimeReasonRefusesSuppressTimeWithAMessage) {
  for (int reason : kSimTimeReasons) {
    SCOPED_TRACE(reason);
    s_vpi_time suppress = {};
    suppress.type = vpiSuppressTime;
    suppress.low = 3;
    s_cb_data cb = {};
    cb.reason = reason;
    cb.cb_rtn = RecordDelivery;
    cb.time = &suppress;
    ExpectRefusedWithAMessage(vpi_register_cb(&cb));
  }
}

PLI_INT32 ArmReadWriteBesideAnUpdate(p_cb_data) {
  PlaceTimeCallback(cbReadOnlySynch, 5, "read-only-5");
  PlaceTimeCallback(cbReadWriteSynch, 5, "read-write-5");
  return 0;
}

TEST_F(TimeCallbacksOfARun,
       AReadWriteSynchFollowsTheEventsAndPrecedesReadOnly) {
  RunArmedBy(&ArmReadWriteBesideAnUpdate,
             "module top; timeunit 1ns; timeprecision 1ns; int q;\n"
             "  initial begin #5; q = 1; q <= 2; #5; end\n"
             "endmodule\n");
  ASSERT_EQ(TimeDeliveries().size(), 2u);
  EXPECT_EQ(TimeDeliveries()[0].label, "read-write-5");
  EXPECT_EQ(TimeDeliveries()[0].time, 5u);
  EXPECT_TRUE(TimeDeliveries()[0].value == 1 || TimeDeliveries()[0].value == 2)
      << TimeDeliveries()[0].value;
  EXPECT_EQ(TimeDeliveries()[1], (TimeDelivery{"read-only-5", 5, 2}));
}

PLI_INT32 ArmStartOfAnEmptyTime(p_cb_data) {
  PlaceTimeCallback(cbAtStartOfSimTime, 3, "start-of-3");
  return 0;
}

TEST_F(TimeCallbacksOfARun, AStartOfSimTimeIsCalledAtATimeWithNoEvent) {
  RunArmedBy(&ArmStartOfAnEmptyTime,
             "module top; timeunit 1ns; timeprecision 1ns; int q;\n"
             "  initial begin #5 q = 1; end\n"
             "endmodule\n");
  EXPECT_EQ(TimeDeliveries(),
            (std::vector<TimeDelivery>{{"start-of-3", 3, 0}}));
}

void PutFourIntoQ(int flag) {
  s_vpi_time delay = {};
  delay.type = vpiSimTime;
  delay.low = 1;
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 4;
  vpi_put_value(vpi_handle_by_name(VpiText("top.q"), nullptr), &value, &delay,
                flag);
  const PLI_INT32 kLevel = vpi_chk_error(nullptr);
  PutRefusals().push_back(kLevel != 0);
}

PLI_INT32 PutWithEveryDelayMode(p_cb_data) {
  PutFourIntoQ(vpiInertialDelay);
  PutFourIntoQ(vpiTransportDelay);
  PutFourIntoQ(vpiPureTransportDelay);
  return 0;
}

PLI_INT32 PutWithForceAndRelease(p_cb_data) {
  PutFourIntoQ(vpiForceFlag);
  PutFourIntoQ(vpiReleaseFlag);
  return 0;
}

PLI_INT32 ArmScheduledPutsFromReadOnly(p_cb_data) {
  PlaceTimeCallback(cbReadOnlySynch, 2, "ro", &PutWithEveryDelayMode);
  return 0;
}

PLI_INT32 ArmForcingPutsFromReadOnly(p_cb_data) {
  PlaceTimeCallback(cbReadOnlySynch, 2, "ro", &PutWithForceAndRelease);
  return 0;
}

constexpr const char* kQuietQ =
    "module top; timeunit 1ns; timeprecision 1ns; int q;\n"
    "  initial #9;\n"
    "endmodule\n";

TEST_F(TimeCallbacksOfARun, APutThatSchedulesFromReadOnlySynchIsRefused) {
  PutRefusals().clear();
  RunArmedBy(&ArmScheduledPutsFromReadOnly, kQuietQ);
  EXPECT_EQ(PutRefusals(), (std::vector<bool>{true, true, true}));
  EXPECT_EQ(IntOfTop("top.q"), 0);
}

TEST_F(TimeCallbacksOfARun, AForceOrReleaseFromReadOnlySynchIsRefused) {
  PutRefusals().clear();
  RunArmedBy(&ArmForcingPutsFromReadOnly, kQuietQ);
  EXPECT_EQ(PutRefusals(), (std::vector<bool>{true, true}));
  EXPECT_EQ(IntOfTop("top.q"), 0);
}

std::vector<uint64_t>& TicksCalledAt() {
  static std::vector<uint64_t> ticks;
  return ticks;
}

PLI_INT32 NoteTicks(p_cb_data) {
  s_vpi_time now = {};
  now.type = vpiSimTime;
  vpi_get_time(nullptr, &now);
  TicksCalledAt().push_back((uint64_t{now.high} << 32) | now.low);
  return 0;
}

PLI_INT32 ArmScaledDelay(p_cb_data) {
  static s_vpi_time scaled = {};
  scaled.type = vpiScaledRealTime;
  scaled.real = 1.5;
  s_cb_data data = {};
  data.reason = cbAfterDelay;
  data.cb_rtn = &NoteTicks;
  data.obj = vpi_handle_by_name(VpiText("top"), nullptr);
  data.time = &scaled;
  vpi_register_cb(&data);
  return 0;
}

TEST_F(TimeCallbacksOfARun,
       DISABLED_AScaledRealDelayIsReadInTheObjectsTimeUnit) {
  TicksCalledAt().clear();
  RunArmedBy(&ArmScaledDelay,
             "module top; timeunit 1ns; timeprecision 100ps;\n"
             "  initial #5;\n"
             "endmodule\n");
  EXPECT_EQ(vpi_get(vpiTimePrecision, nullptr), -10);
  EXPECT_EQ(TicksCalledAt(), (std::vector<uint64_t>{15}));
}

struct ZeroDelayPlacement {
  bool placed = false;
  int level = 0;
  bool has_message = false;
  bool operator==(const ZeroDelayPlacement&) const = default;
};

std::vector<ZeroDelayPlacement>& ZeroDelayPlacements() {
  static std::vector<ZeroDelayPlacement> placements;
  return placements;
}

void PlaceZeroDelayAndNote(int reason) {
  static s_vpi_time zero = {vpiSimTime, 0, 0, 0};
  s_cb_data data = {};
  data.reason = reason;
  data.cb_rtn = &RecordTimeDelivery;
  data.time = &zero;
  data.user_data = VpiText("zero-delay");
  vpiHandle placed = vpi_register_cb(&data);
  s_vpi_error_info info = {};
  const PLI_INT32 kLevel = vpi_chk_error(&info);
  ZeroDelayPlacements().push_back(
      {placed != nullptr, kLevel,
       kLevel != 0 && info.message != nullptr && info.message[0] != '\0'});
}

PLI_INT32 PlaceStartOfThisTime(p_cb_data) {
  PlaceZeroDelayAndNote(cbAtStartOfSimTime);
  return 0;
}

PLI_INT32 PlaceReadWriteOfThisTime(p_cb_data) {
  PlaceZeroDelayAndNote(cbReadWriteSynch);
  return 0;
}

PLI_INT32 ArmStartOfTwoFromReadWrite(p_cb_data) {
  PlaceTimeCallback(cbReadWriteSynch, 2, "rw", &PlaceStartOfThisTime);
  return 0;
}

PLI_INT32 ArmReadWriteOfFourFromReadOnly(p_cb_data) {
  PlaceTimeCallback(cbReadOnlySynch, 4, "ro", &PlaceReadWriteOfThisTime);
  return 0;
}

void ExpectTheOnePlacementRefused() {
  EXPECT_EQ(ZeroDelayPlacements(),
            (std::vector<ZeroDelayPlacement>{{false, vpiError, true}}));
  EXPECT_TRUE(TimeDeliveries().empty());
}

TEST_F(TimeCallbacksOfARun,
       DISABLED_AZeroDelayStartOfSimTimeMidSliceIsRefusedWithAnError) {
  ZeroDelayPlacements().clear();
  RunArmedBy(&ArmStartOfTwoFromReadWrite, kQuietQ);
  ExpectTheOnePlacementRefused();
}

TEST_F(TimeCallbacksOfARun,
       AZeroDelayReadWriteSynchFromReadOnlyIsRefusedWithAnError) {
  ZeroDelayPlacements().clear();
  RunArmedBy(&ArmReadWriteOfFourFromReadOnly, kQuietQ);
  ExpectTheOnePlacementRefused();
}

PLI_INT32 ArmStartOfFourAgain(p_cb_data) {
  PlaceTimeCallback(cbAtStartOfSimTime, 4, "start-of-4", &PlaceStartOfThisTime);
  return 0;
}

TEST_F(TimeCallbacksOfARun, AStartOfSimTimePlacedFromOneRunsInTheSameSlice) {
  ZeroDelayPlacements().clear();
  RunArmedBy(&ArmStartOfFourAgain, kQuietQ);
  ASSERT_EQ(ZeroDelayPlacements().size(), 1u);
  EXPECT_TRUE(ZeroDelayPlacements()[0].placed);
  EXPECT_EQ(TimeDeliveries(),
            (std::vector<TimeDelivery>{{"zero-delay", 4, 0}}));
}

}  // namespace
}  // namespace delta
