#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §38.36.1 covers the simulation-event callback reasons registered through
// vpi_register_cb(). The single registration-time rule this subclause's text
// states - distinct from the firing semantics of the individual reasons - is
// that a cbForce, cbRelease, or cbDisable callback may not be placed on a
// variable bit-select. These tests observe vpi_register_cb() applying that
// rule.
class VpiSimEventCb : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // Build a handle to a single bit-select of a declared variable.
  vpiHandle MakeBitSelectHandle(const char* name) {
    sim_ctx_.CreateVariable(name, 1);
    vpi_ctx_.Attach(sim_ctx_);
    vpiHandle h = vpi_handle_by_name(name, nullptr);
    if (h) h->type = vpiBitSelect;
    return h;
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

// §38.36.1: placing a cbForce callback on a variable bit-select is illegal;
// vpi_register_cb() rejects it and reports an error.
TEST_F(VpiSimEventCb, ForceCallbackOnBitSelectRejected) {
  vpiHandle bit = MakeBitSelectHandle("f");
  ASSERT_NE(bit, nullptr);

  s_cb_data cb = {};
  cb.reason = cbForce;
  cb.obj = bit;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
}

// §38.36.1: the same prohibition holds for a cbRelease callback.
TEST_F(VpiSimEventCb, ReleaseCallbackOnBitSelectRejected) {
  vpiHandle bit = MakeBitSelectHandle("r");
  ASSERT_NE(bit, nullptr);

  s_cb_data cb = {};
  cb.reason = cbRelease;
  cb.obj = bit;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
}

// §38.36.1: and for a cbDisable callback.
TEST_F(VpiSimEventCb, DisableCallbackOnBitSelectRejected) {
  vpiHandle bit = MakeBitSelectHandle("d");
  ASSERT_NE(bit, nullptr);

  s_cb_data cb = {};
  cb.reason = cbDisable;
  cb.obj = bit;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
}

// §38.36.1: the prohibition is specific to a bit-select target. A cbForce
// callback on the whole variable (not a bit-select) is a legal registration and
// produces a callback handle.
TEST_F(VpiSimEventCb, ForceCallbackOnWholeVariableAccepted) {
  sim_ctx_.CreateVariable("whole", 1);
  vpi_ctx_.Attach(sim_ctx_);
  vpiHandle var = vpi_handle_by_name("whole", nullptr);
  ASSERT_NE(var, nullptr);

  s_cb_data cb = {};
  cb.reason = cbForce;
  cb.obj = var;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

// §38.36.1: for a force/release callback a NULL obj means every force or
// release should generate a callback - it is not a bit-select, so registration
// is accepted rather than rejected by the bit-select rule.
TEST_F(VpiSimEventCb, ForceCallbackWithNullObjectAccepted) {
  s_cb_data cb = {};
  cb.reason = cbForce;
  cb.obj = nullptr;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

// §38.36.1: the prohibition names only cbForce, cbRelease, and cbDisable. A
// callback for a different reason (here cbValueChange) on the same variable
// bit-select is outside the rule and is registered normally.
TEST_F(VpiSimEventCb, ValueChangeCallbackOnBitSelectAccepted) {
  vpiHandle bit = MakeBitSelectHandle("v");
  ASSERT_NE(bit, nullptr);

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = bit;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

// A recording callback routine, used to observe what the simulator delivers to
// a simulation-event callback when it fires. §38.36.1 states that the routine
// is handed a pointer to an s_cb_data structure (not the one supplied at
// registration) whose fields the simulator has shaped for the reason.
int g_deliver_calls = 0;
VpiCbData* g_delivered_ptr = nullptr;
int g_delivered_reason = 0;
VpiTime* g_delivered_time = nullptr;
VpiValue* g_delivered_value = nullptr;
void* g_delivered_user_data = nullptr;
VpiHandle g_delivered_obj = nullptr;

int RecordDelivery(VpiCbData* data) {
  ++g_deliver_calls;
  g_delivered_ptr = data;
  if (data) {
    g_delivered_reason = data->reason;
    g_delivered_time = data->time;
    g_delivered_value = data->value;
    g_delivered_user_data = data->user_data;
    g_delivered_obj = data->obj;
  }
  return 0;
}

// Fixture for the delivery-time rules of §38.36.1: what the simulator passes to
// the routine when a simulation-event callback fires.
class VpiSimEventCbDelivery : public ::testing::Test {
 protected:
  void SetUp() override {
    g_deliver_calls = 0;
    g_delivered_ptr = nullptr;
    g_delivered_reason = 0;
    g_delivered_time = nullptr;
    g_delivered_value = nullptr;
    g_delivered_user_data = nullptr;
    g_delivered_obj = nullptr;
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

// §38.36.1: a cbReclaimObj callback has no relationship to simulation time, so
// the time field passed to the routine is NULL - even though a time structure
// with a concrete type was supplied at registration.
TEST_F(VpiSimEventCbDelivery, ReclaimObjCallbackDeliveredWithoutTime) {
  VpiTime requested = {};
  requested.type = vpiSimTime;

  s_cb_data cb = {};
  cb.reason = cbReclaimObj;
  cb.cb_rtn = &RecordDelivery;
  cb.time = &requested;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  int fired = vpi_ctx_.DispatchCallbacks(cbReclaimObj);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_deliver_calls, 1);
  EXPECT_EQ(g_delivered_reason, cbReclaimObj);
  // The time->type supplied at registration is ignored; no time is passed.
  EXPECT_EQ(g_delivered_time, nullptr);
}

// §38.36.1: for cbEndOfObject as well, time information is not passed to the
// callback routine, so the delivered time pointer is NULL.
TEST_F(VpiSimEventCbDelivery, EndOfObjectCallbackDeliveredWithoutTime) {
  VpiTime requested = {};
  requested.type = vpiScaledRealTime;

  s_cb_data cb = {};
  cb.reason = cbEndOfObject;
  cb.cb_rtn = &RecordDelivery;
  cb.time = &requested;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  int fired = vpi_ctx_.DispatchCallbacks(cbEndOfObject);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_delivered_time, nullptr);
}

// §38.36.1 (negative form of the time-drop rule): the rule names only
// cbReclaimObj and cbEndOfObject. A different simulation-event reason keeps the
// time structure the application requested, so the routine still sees it.
TEST_F(VpiSimEventCbDelivery, ValueChangeCallbackKeepsRequestedTime) {
  VpiTime requested = {};
  requested.type = vpiSimTime;

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = &RecordDelivery;
  cb.time = &requested;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  int fired = vpi_ctx_.DispatchCallbacks(cbValueChange);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_delivered_time, &requested);
}

// §38.36.1: when a simulation-event callback occurs the routine is passed a
// pointer to an s_cb_data structure that is not the one supplied at
// registration, and its user_data field is equivalent to the one that was
// passed to vpi_register_cb().
TEST_F(VpiSimEventCbDelivery,
       SimEventCallbackDeliversFreshStructPreservingUserData) {
  int payload = 42;
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = &RecordDelivery;
  cb.user_data = &payload;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  int fired = vpi_ctx_.DispatchCallbacks(cbValueChange);

  EXPECT_EQ(fired, 1);
  // Not the structure passed to vpi_register_cb().
  EXPECT_NE(g_delivered_ptr, &cb);
  // user_data reaches the routine unchanged.
  EXPECT_EQ(g_delivered_user_data, &payload);
}

// §38.36.1: for a cbForce callback the obj field delivered to the routine is a
// handle to the force statement, which the simulator supplies when it fires the
// callback.
TEST_F(VpiSimEventCbDelivery, ForceCallbackDeliversForceStatementHandle) {
  VpiObject force_stmt;
  s_cb_data cb = {};
  cb.reason = cbForce;
  cb.cb_rtn = &RecordDelivery;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  int fired = vpi_ctx_.DispatchCallbacks(cbForce, &force_stmt);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_delivered_obj, &force_stmt);
}

// §38.36.1: the obj-is-the-statement rule covers cbRelease as well as cbForce;
// a cbRelease callback is delivered a handle to the release statement.
TEST_F(VpiSimEventCbDelivery, ReleaseCallbackDeliversReleaseStatementHandle) {
  VpiObject release_stmt;
  s_cb_data cb = {};
  cb.reason = cbRelease;
  cb.cb_rtn = &RecordDelivery;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  int fired = vpi_ctx_.DispatchCallbacks(cbRelease, &release_stmt);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_delivered_obj, &release_stmt);
}

// §38.36.1: a cbAssign callback - fired after a procedural assign statement -
// is likewise delivered a handle to that assign statement in obj.
TEST_F(VpiSimEventCbDelivery, AssignCallbackDeliversAssignStatementHandle) {
  VpiObject assign_stmt;
  s_cb_data cb = {};
  cb.reason = cbAssign;
  cb.cb_rtn = &RecordDelivery;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  int fired = vpi_ctx_.DispatchCallbacks(cbAssign, &assign_stmt);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_delivered_reason, cbAssign);
  EXPECT_EQ(g_delivered_obj, &assign_stmt);
}

// §38.36.1: and a cbDeassign callback is delivered a handle to the deassign
// statement, completing the four force/release/assign/deassign reasons whose
// obj field is the responsible statement.
TEST_F(VpiSimEventCbDelivery, DeassignCallbackDeliversDeassignStatementHandle) {
  VpiObject deassign_stmt;
  s_cb_data cb = {};
  cb.reason = cbDeassign;
  cb.cb_rtn = &RecordDelivery;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  int fired = vpi_ctx_.DispatchCallbacks(cbDeassign, &deassign_stmt);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_delivered_reason, cbDeassign);
  EXPECT_EQ(g_delivered_obj, &deassign_stmt);
}

// §38.36.1: for a cbDisable callback the obj field is a handle to the disabled
// construct - a system task call, system function call, named begin, named
// fork, task, or function. The simulator supplies that handle when it fires the
// callback, so the routine sees it in obj.
TEST_F(VpiSimEventCbDelivery, DisableCallbackDeliversDisabledConstructHandle) {
  VpiObject disabled_task;
  s_cb_data cb = {};
  cb.reason = cbDisable;
  cb.cb_rtn = &RecordDelivery;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  int fired = vpi_ctx_.DispatchCallbacks(cbDisable, &disabled_task);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_delivered_reason, cbDisable);
  EXPECT_EQ(g_delivered_obj, &disabled_task);
}

// §38.36.1: a cbValueChange callback may be placed on an event statement. Since
// an event statement has no value, the value field the routine receives is
// NULL, even though a value structure was supplied at registration. Here the
// obj is the named-event object the trigger acts on.
TEST_F(VpiSimEventCbDelivery, ValueChangeOnNamedEventDeliversNullValue) {
  VpiObject named_event;
  named_event.type = vpiNamedEvent;
  VpiValue requested = {};

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = &RecordDelivery;
  cb.value = &requested;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  int fired = vpi_ctx_.DispatchCallbacks(cbValueChange, &named_event);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_delivered_value, nullptr);
}

// §38.36.1: the same value-is-NULL delivery holds when the watched object is an
// event statement itself, the other event-statement input form.
TEST_F(VpiSimEventCbDelivery, ValueChangeOnEventStatementDeliversNullValue) {
  VpiObject event_stmt;
  event_stmt.type = vpiEventStmt;
  VpiValue requested = {};

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = &RecordDelivery;
  cb.value = &requested;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  int fired = vpi_ctx_.DispatchCallbacks(cbValueChange, &event_stmt);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_delivered_value, nullptr);
}

// §38.36.1: a cbValueChange callback may be placed on a class variable. Its
// value is an opaque handle to a dynamic object and cannot be read through the
// value field, so the routine receives a NULL value field (the referenced
// object is identified through vpiObjId instead).
TEST_F(VpiSimEventCbDelivery, ValueChangeOnClassVarDeliversNullValue) {
  VpiObject class_var;
  class_var.type = vpiClassVar;
  VpiValue requested = {};

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = &RecordDelivery;
  cb.value = &requested;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  int fired = vpi_ctx_.DispatchCallbacks(cbValueChange, &class_var);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_delivered_value, nullptr);
}

// §38.36.1 (negative form of the value-is-NULL rule): the NULL-value delivery
// is specific to valueless/opaque objects. A cbValueChange callback on an
// ordinary declared variable keeps the value structure the application
// requested, so the routine still sees it.
TEST_F(VpiSimEventCbDelivery, ValueChangeOnOrdinaryVariableKeepsValue) {
  sim_ctx_.CreateVariable("ord", 1);
  vpi_ctx_.Attach(sim_ctx_);
  vpiHandle var = vpi_handle_by_name("ord", nullptr);
  ASSERT_NE(var, nullptr);
  VpiValue requested = {};

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = &RecordDelivery;
  cb.value = &requested;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  int fired = vpi_ctx_.DispatchCallbacks(cbValueChange, var);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_delivered_value, &requested);
}

}  // namespace
}  // namespace delta
