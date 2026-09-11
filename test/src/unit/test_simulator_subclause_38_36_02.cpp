#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §38.36.2: the simulation-time reasons that vpi_register_cb() constrains
// through the s_cb_data time structure.
const int kSimTimeReasons[] = {
    cbAtStartOfSimTime, cbNBASynch,    cbReadWriteSynch, cbAtEndOfSimTime,
    cbReadOnlySynch,    cbNextSimTime, cbAfterDelay,
};

// A routine that, when a callback fires, registers a zero-delay
// cbAtStartOfSimTime callback. The §38.36.2 carve-out allows this only because
// it runs from within a cbAtStartOfSimTime callback.
bool g_inner_called = false;
vpiHandle g_inner_handle = nullptr;
int RegisterZeroDelayWithinCallback(VpiCbData*) {
  g_inner_called = true;
  static VpiTime t = {};
  t.type = vpiSimTime;  // low/high/real all zero -> zero delay
  s_cb_data inner = {};
  inner.reason = cbAtStartOfSimTime;
  inner.time = &t;
  g_inner_handle = vpi_register_cb(&inner);
  return 0;
}

// What a simulation-time callback's routine was handed, recorded so the test
// can read it after the dispatch returns. §38.36.2 gives the routine a single
// argument - a pointer to an s_cb_data that is not the one registration was
// given - so the pointer itself is recorded alongside the fields.
struct DeliveredCbData {
  const VpiCbData* structure = nullptr;
  bool had_time = false;
  int time_type = 0;
  uint32_t time_low = 0;
  uint32_t time_high = 0;
  double time_real = 0.0;
  bool had_value = false;
  void* user_data = nullptr;
};
DeliveredCbData g_delivered;
int RecordDelivery(VpiCbData* data) {
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

  // Advance the simulation clock to `t` by draining a no-op event scheduled
  // there; after Run() the scheduler's current time is that slot.
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

// §38.36.2: the seven time-related callback reasons are defined and may be
// registered through vpi_register_cb() when given a valid time structure.
TEST_F(VpiSimTimeCallbacks, AllSimTimeReasonsRegisterWithValidTime) {
  for (int reason : kSimTimeReasons) {
    VpiTime t = {};
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

// §38.36.2: a null time pointer leaves no time for a simulation-time callback,
// so registration is an error and no callback is created.
TEST_F(VpiSimTimeCallbacks, NullTimeStructureIsRejected) {
  s_cb_data cb = {};
  cb.reason = cbAtEndOfSimTime;
  cb.time = nullptr;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);
}

// §38.36.2: a time->type of vpiSuppressTime is explicitly an error for a
// simulation-time callback.
TEST_F(VpiSimTimeCallbacks, SuppressTimeTypeIsRejected) {
  VpiTime t = {};
  t.type = vpiSuppressTime;
  s_cb_data cb = {};
  cb.reason = cbNBASynch;
  cb.time = &t;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);
}

// §38.36.2: the time-structure requirement is scoped to the simulation-time
// reasons. A reason that is not one of them (here an action callback) still
// registers with no time structure at all.
TEST_F(VpiSimTimeCallbacks, NonSimTimeReasonIgnoresTimeRequirement) {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  cb.time = nullptr;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

// §38.36.2: placing a cbAtStartOfSimTime callback with a delay of zero once
// simulation has progressed into a time slice - and not from within a
// cbAtStartOfSimTime callback - is an error.
TEST_F(VpiSimTimeCallbacks, ZeroDelayAtStartOfSimTimeRejectedAfterTimeSlice) {
  vpi_ctx_.SetSimulationProgressedIntoTimeSlice(true);

  VpiTime t = {};
  t.type = vpiSimTime;  // zero delay
  s_cb_data cb = {};
  cb.reason = cbAtStartOfSimTime;
  cb.time = &t;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);
}

// §38.36.2: the same placement with a non-zero delay is permitted even after
// simulation has entered a time slice - only the zero-delay case is barred.
TEST_F(VpiSimTimeCallbacks, NonZeroDelayAtStartOfSimTimeAllowedAfterTimeSlice) {
  vpi_ctx_.SetSimulationProgressedIntoTimeSlice(true);

  VpiTime t = {};
  t.type = vpiSimTime;
  t.low = 1;  // non-zero delay
  s_cb_data cb = {};
  cb.reason = cbAtStartOfSimTime;
  cb.time = &t;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

// §38.36.2: the zero-delay cbAtStartOfSimTime restriction applies only once
// simulation has progressed into a time slice. Before that - the default state,
// e.g. at time zero - a zero-delay cbAtStartOfSimTime callback is accepted.
TEST_F(VpiSimTimeCallbacks, ZeroDelayAtStartOfSimTimeAllowedBeforeTimeSlice) {
  // SetSimulationProgressedIntoTimeSlice is left at its default of false.
  VpiTime t = {};
  t.type = vpiSimTime;  // zero delay
  s_cb_data cb = {};
  cb.reason = cbAtStartOfSimTime;
  cb.time = &t;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

// §38.36.2: placing a zero-delay cbAtStartOfSimTime callback during a
// cbAtStartOfSimTime callback is allowed, producing another callback in the
// same time slice. Dispatching the outer callback sets the current reason, so
// the inner zero-delay registration succeeds despite the time slice being
// active.
TEST_F(VpiSimTimeCallbacks, ZeroDelayAtStartOfSimTimeAllowedWithinCallback) {
  vpi_ctx_.SetSimulationProgressedIntoTimeSlice(true);

  VpiTime outer_t = {};
  outer_t.type = vpiSimTime;
  outer_t.low = 1;  // non-zero delay so the outer callback itself registers
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

// §38.36.2: a zero-delay cbReadWriteSynch callback may not be placed at
// read-only synch time.
TEST_F(VpiSimTimeCallbacks, ZeroDelayReadWriteSynchRejectedAtReadOnlySynch) {
  vpi_ctx_.SetAtReadOnlySynchTime(true);

  VpiTime t = {};
  t.type = vpiSimTime;  // zero delay
  s_cb_data cb = {};
  cb.reason = cbReadWriteSynch;
  cb.time = &t;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);
}

// §38.36.2: the same zero-delay cbReadWriteSynch placement is permitted when
// the simulation is not at read-only synch time.
TEST_F(VpiSimTimeCallbacks, ZeroDelayReadWriteSynchAllowedWhenNotReadOnly) {
  VpiTime t = {};
  t.type = vpiSimTime;  // zero delay, but not at read-only synch
  s_cb_data cb = {};
  cb.reason = cbReadWriteSynch;
  cb.time = &t;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

// §38.36.2: at read-only synch time only a zero-delay cbReadWriteSynch callback
// is barred; one with a non-zero delay is still accepted there.
TEST_F(VpiSimTimeCallbacks, NonZeroDelayReadWriteSynchAllowedAtReadOnlySynch) {
  vpi_ctx_.SetAtReadOnlySynchTime(true);

  VpiTime t = {};
  t.type = vpiSimTime;
  t.low = 1;  // non-zero delay
  s_cb_data cb = {};
  cb.reason = cbReadWriteSynch;
  cb.time = &t;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

// §38.36.2: the requested delay is carried across the whole time value, not the
// low word alone. A delay set only in the high word is still non-zero, so the
// zero-delay cbAtStartOfSimTime restriction does not apply and registration
// succeeds even after simulation has entered a time slice.
TEST_F(VpiSimTimeCallbacks, HighWordDelayCountsAsNonZeroForAtStartOfSimTime) {
  vpi_ctx_.SetSimulationProgressedIntoTimeSlice(true);

  VpiTime t = {};
  t.type = vpiSimTime;
  t.low = 0;
  t.high = 1;  // non-zero delay carried entirely in the high word
  s_cb_data cb = {};
  cb.reason = cbAtStartOfSimTime;
  cb.time = &t;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

// §38.36.2: for vpiScaledRealTime the delay lives in the real field. A non-zero
// real delay is likewise non-zero, lifting the zero-delay cbAtStartOfSimTime
// restriction even after the simulation has entered a time slice.
TEST_F(VpiSimTimeCallbacks, RealDelayCountsAsNonZeroForAtStartOfSimTime) {
  vpi_ctx_.SetSimulationProgressedIntoTimeSlice(true);

  VpiTime t = {};
  t.type = vpiScaledRealTime;
  t.low = 0;
  t.high = 0;
  t.real = 1.0;  // non-zero delay carried in the real field
  s_cb_data cb = {};
  cb.reason = cbAtStartOfSimTime;
  cb.time = &t;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

// §38.36.2: "When a simulation time callback occurs, the application callback
// routine shall be passed a single argument, which is a pointer to an s_cb_data
// structure [this is not a pointer to the same structure that was passed to
// vpi_register_cb()]. The time structure shall contain the current simulation
// time. The user_data field shall be equivalent to the user_data field passed
// to vpi_register_cb()." The routine was handed the time the registration asked
// the callback to fire at - a delay, or a moment still ahead - rather than the
// time the simulation had reached when it fired.
TEST_F(VpiSimTimeCallbacks, RoutineIsPassedTheCurrentTimeAndItsOwnStructure) {
  AdvanceTo(40);

  int user_object = 7;
  VpiTime requested = {};
  requested.type = vpiSimTime;
  requested.low = 5;  // the delay asked for, not the time of the firing
  s_cb_data cb = {};
  cb.reason = cbAfterDelay;
  cb.time = &requested;
  cb.cb_rtn = RecordDelivery;
  cb.user_data = &user_object;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbAfterDelay), 1);
  ASSERT_TRUE(g_delivered.had_time);
  EXPECT_EQ(g_delivered.time_type, vpiSimTime);
  EXPECT_EQ(g_delivered.time_low, 40u);
  EXPECT_EQ(g_delivered.time_high, 0u);
  EXPECT_EQ(g_delivered.user_data, &user_object);

  // The structure the routine saw is not the one registration was given, and
  // the request it was given is left as it was written.
  EXPECT_NE(g_delivered.structure, &cb);
  EXPECT_EQ(requested.low, 5u);
}

// §38.36.2: "The value fields are ignored for all reasons with simulation time
// callbacks", so a routine sees no value however the registration was written,
// and this holds for each of the seven reasons.
TEST_F(VpiSimTimeCallbacks, EveryReasonDeliversTheCurrentTimeAndNoValue) {
  AdvanceTo(12);

  for (int reason : kSimTimeReasons) {
    g_delivered = DeliveredCbData{};

    s_vpi_value value = {};
    value.format = vpiIntVal;
    VpiTime requested = {};
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

// §38.36.2: "When the cb_data_p->time->type is set to vpiScaledRealTime, the
// cb_data_p->obj field shall be used as the object for determining the time
// scaling." The form the registration asked for is kept, so the current time
// reaches the routine as a real scaled to that object's time unit.
TEST_F(VpiSimTimeCallbacks, ScaledRealTimeIsScaledToTheObjFieldsTimeUnit) {
  vpi_ctx_.SetSimTimeUnit(-12);  // the run counts in picoseconds
  AdvanceTo(3000);

  VpiHandle scope = vpi_ctx_.CreateModule("m", "m");
  scope->time_unit = -9;  // and this object is written in nanoseconds

  VpiTime requested = {};
  requested.type = vpiScaledRealTime;
  requested.real = 1.0;
  s_cb_data cb = {};
  cb.reason = cbReadOnlySynch;
  cb.time = &requested;
  cb.obj = scope;
  cb.cb_rtn = RecordDelivery;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbReadOnlySynch), 1);
  ASSERT_TRUE(g_delivered.had_time);
  EXPECT_EQ(g_delivered.time_type, vpiScaledRealTime);
  EXPECT_DOUBLE_EQ(g_delivered.time_real, 3.0);  // 3000 ps read as 3 ns
}

// §38.36.2: "For reason cbNextSimTime, the time field in the time structure is
// ignored." The type is still required - it selects the form the routine is
// given - but the requested time itself decides nothing, so a registration
// carrying any value at all is accepted and the routine is handed the current
// time like every other simulation-time reason.
TEST_F(VpiSimTimeCallbacks, NextSimTimeIgnoresTheTimeItWasRegisteredWith) {
  AdvanceTo(8);

  VpiTime requested = {};
  requested.type = vpiSimTime;
  requested.low = 0xFFFFFFFFu;
  requested.high = 0xFFFFFFFFu;
  s_cb_data cb = {};
  cb.reason = cbNextSimTime;
  cb.time = &requested;
  cb.cb_rtn = RecordDelivery;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbNextSimTime), 1);
  ASSERT_TRUE(g_delivered.had_time);
  EXPECT_EQ(g_delivered.time_low, 8u);
  EXPECT_EQ(g_delivered.time_high, 0u);
}

// The delivery rule is scoped to the simulation-time reasons: a callback
// registered for a reason outside them keeps the time and value its
// registration carried, which is what §38.36.1 and §38.36.3 give their own
// reasons.
TEST_F(VpiSimTimeCallbacks, ANonSimTimeReasonKeepsTheTimeItWasRegisteredWith) {
  AdvanceTo(25);

  s_vpi_value value = {};
  value.format = vpiIntVal;
  VpiTime requested = {};
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

}  // namespace
}  // namespace delta
