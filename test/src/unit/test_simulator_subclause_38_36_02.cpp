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
int RegisterZeroDelayWithinCallback(s_cb_data*) {
  g_inner_called = true;
  static s_vpi_time t = {};
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
  s_vpi_time t = {};
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

  s_vpi_time t = {};
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

  s_vpi_time t = {};
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
  s_vpi_time t = {};
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

  s_vpi_time outer_t = {};
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

  s_vpi_time t = {};
  t.type = vpiSimTime;  // zero delay
  s_cb_data cb = {};
  cb.reason = cbReadWriteSynch;
  cb.time = &t;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);
}

// §38.36.2: the same zero-delay cbReadWriteSynch placement is permitted when
// the simulation is not at read-only synch time.
TEST_F(VpiSimTimeCallbacks, ZeroDelayReadWriteSynchAllowedWhenNotReadOnly) {
  s_vpi_time t = {};
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

  s_vpi_time t = {};
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

  s_vpi_time t = {};
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

  s_vpi_time t = {};
  t.type = vpiScaledRealTime;
  t.low = 0;
  t.high = 0;
  t.real = 1.0;  // non-zero delay carried in the real field
  s_cb_data cb = {};
  cb.reason = cbAtStartOfSimTime;
  cb.time = &t;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

// §38.36.2: a simulation time callback hands its routine one argument, a
// pointer to an s_cb_data structure other than the one vpi_register_cb() was
// given, whose time structure holds the current simulation time and whose
// user_data matches the user_data the registration passed. The routine was
// handed the time the registration asked the callback to fire at - a delay, or
// a moment still ahead - rather than the time the simulation had reached when
// it fired.
TEST_F(VpiSimTimeCallbacks, RoutineIsPassedTheCurrentTimeAndItsOwnStructure) {
  AdvanceTo(40);

  int user_object = 7;
  s_vpi_time requested = {};
  requested.type = vpiSimTime;
  requested.low = 5;  // the delay asked for, not the time of the firing
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

  // The structure the routine saw is not the one registration was given, and
  // the request it was given is left as it was written.
  EXPECT_NE(g_delivered.structure, &cb);
  EXPECT_EQ(requested.low, 5u);
}

// §38.36.2: no simulation time reason reads the value fields, so a routine sees
// no value however the registration was written, and this holds for each reason
// due in the slot it was registered in, which is every one but cbNextSimTime
// (NextSimTimeIgnoresTheTimeItWasRegisteredWith covers that one).
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

// §38.36.2: with cb_data_p->time->type set to vpiScaledRealTime, the object in
// cb_data_p->obj is what the time is scaled by. The form the registration asked
// for is kept, so the current time reaches the routine as a real scaled to that
// object's time unit.
TEST_F(VpiSimTimeCallbacks, ScaledRealTimeIsScaledToTheObjFieldsTimeUnit) {
  vpi_ctx_.SetSimTimeUnit(-12);  // the run counts in picoseconds
  AdvanceTo(3000);

  VpiHandle scope = vpi_ctx_.CreateModule("m", "m");
  scope->time_unit = -9;  // and this object is written in nanoseconds

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
  EXPECT_DOUBLE_EQ(g_delivered.time_real, 3.0);  // 3000 ps read as 3 ns
}

// §38.36.2: cbNextSimTime does not read the time field of the time structure.
// The type is still required - it selects the form the routine is given - but
// the requested time itself decides nothing, so a registration carrying any
// value at all is accepted and the routine is handed, before the next time
// slot's events, that slot's time and no value, like every other
// simulation-time reason.
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

// The delivery rule is scoped to the simulation-time reasons: a callback
// registered for a reason outside them keeps the time and value its
// registration carried, which is what §38.36.1 and §38.36.3 give their own
// reasons.
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

// What a simulation-time callback's routine saw: the label it was registered
// with, the time it was given and the value of `top.<watched>` then.
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

// Registers a `reason` callback `delay` ticks from now, labelled `label`.
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

// A run whose cbStartOfSimulation routine is `arm`.
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

PLI_INT32 ArmEveryTimeReason(p_cb_data /*cb*/) {
  PlaceTimeCallback(cbAtStartOfSimTime, 5, "start-of-5");
  PlaceTimeCallback(cbNBASynch, 5, "nba-synch-5");
  PlaceTimeCallback(cbAtEndOfSimTime, 5, "end-of-5");
  PlaceTimeCallback(cbReadOnlySynch, 5, "read-only-5");
  PlaceTimeCallback(cbAfterDelay, 7, "after-delay-7");
  PlaceTimeCallback(cbNextSimTime, 0, "next-sim-time");
  return 0;
}

// §38.36.2 with §4.4.3: each simulation-time callback is called once at its
// point of the time slot its time gives: cbNextSimTime before the slot after
// the one it was registered in, cbAtStartOfSimTime before the slot's active
// events, cbNBASynch before its nonblocking updates, cbAtEndOfSimTime and
// cbReadOnlySynch after them, and cbAfterDelay after its delay, though no
// event of the design stands at that time (#5117).
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

// Whether each put the case made from a callback was refused, in order.
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

PLI_INT32 ArmSynchWrites(p_cb_data /*cb*/) {
  PlaceTimeCallback(cbReadWriteSynch, 2, "rw", &PutIntoQ);
  PlaceTimeCallback(cbReadOnlySynch, 2, "ro", &PutIntoQ);
  return 0;
}

// §38.36.2: a value may be written from a cbReadWriteSynch routine, but not
// from a cbReadOnlySynch one, whose put is refused with an error and leaves
// the object as it was (#5118).
TEST_F(TimeCallbacksOfARun, APutFromReadOnlySynchIsRefused) {
  PutRefusals().clear();
  RunArmedBy(&ArmSynchWrites,
             "module top; timeunit 1ns; timeprecision 1ns; int q;\n"
             "  initial #3;\n"
             "endmodule\n");
  EXPECT_EQ(PutRefusals(), (std::vector<bool>{false, true}));
  EXPECT_EQ(IntOfTop("top.q"), 3);
}

}  // namespace
}  // namespace delta
