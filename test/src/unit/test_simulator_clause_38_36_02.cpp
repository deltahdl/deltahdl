#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
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

class VpiSimTimeCallbacks : public ::testing::Test {
 protected:
  void SetUp() override {
    g_inner_called = false;
    g_inner_handle = nullptr;
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

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

}  // namespace
}  // namespace delta
