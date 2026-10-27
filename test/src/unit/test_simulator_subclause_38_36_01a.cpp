#include <gtest/gtest.h>

#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_event_callbacks.h"
#include "parser/ast_stmt.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §38.36.1 covers the simulation-event callback reasons registered through
// vpi_register_cb(). Two registration-time rules follow from this subclause's
// text - distinct from the firing semantics of the individual reasons: a
// cbForce, cbRelease, or cbDisable callback may not be placed on a variable
// bit-select, and a callback about one object's change of value or size is
// placed on an object, the obj field holding NULL with a meaning for a force
// or release alone. These tests observe vpi_register_cb() applying both rules.
class VpiSimEventCb : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // Build a handle to a single bit-select of a declared variable.
  vpiHandle MakeBitSelectHandle(const char* name) {
    sim_ctx_.CreateVariable(name, 1);
    vpi_ctx_.Attach(sim_ctx_);
    vpiHandle h = vpi_handle_by_name(VpiText(name), nullptr);
    if (h) VpiObjectOf(h)->type = vpiBitSelect;
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

  s_vpi_error_info info = {};
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

  s_vpi_error_info info = {};
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

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
}

// §38.36.1: the obj field holds the object a callback is for, and a NULL one
// means something for a force or release callback alone. A value change
// callback placed on no object names nothing whose value could change, so
// vpi_register_cb() refuses it and reports why.
TEST_F(VpiSimEventCb, ValueChangeCallbackOnNoObjectRejected) {
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_STREQ(info.message,
               "vpi_register_cb(): a callback for this reason must be placed "
               "on an object");
}

// §38.36.1 and §38.36.1.1: so is every other callback about the one object its
// obj field names: a size change of an array, queue or string, a statement
// about to run, a disable of a block, task or call, and the making (on a class
// typespec) or reclaiming (on one, or on a class object) of class objects.
TEST_F(VpiSimEventCb, EveryCallbackAboutOneObjectIsRejectedOnNoObject) {
  for (int reason :
       {cbSizeChange, cbStmt, cbDisable, cbCreateObj, cbReclaimObj}) {
    s_cb_data cb = {};
    cb.reason = reason;
    EXPECT_EQ(vpi_register_cb(&cb), nullptr) << "reason " << reason;
    s_vpi_error_info info = {};
    EXPECT_EQ(vpi_chk_error(&info), vpiError) << "reason " << reason;
  }
}

// §38.36.1: a NULL obj stands for every force or release, so a force or
// release callback placed on no object is accepted.
TEST_F(VpiSimEventCb, ForceAndReleaseCallbacksOnNoObjectAccepted) {
  for (int reason : {cbForce, cbRelease}) {
    s_cb_data cb = {};
    cb.reason = reason;
    EXPECT_NE(vpi_register_cb(&cb), nullptr) << "reason " << reason;
  }
}

// §38.36.1: the prohibition is specific to a bit-select target. A cbForce
// callback on the whole variable (not a bit-select) is a legal registration and
// produces a callback handle.
TEST_F(VpiSimEventCb, ForceCallbackOnWholeVariableAccepted) {
  sim_ctx_.CreateVariable("whole", 1);
  vpi_ctx_.Attach(sim_ctx_);
  vpiHandle var = vpi_handle_by_name(VpiText("whole"), nullptr);
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
s_cb_data* g_delivered_ptr = nullptr;
int g_delivered_reason = 0;
s_vpi_time* g_delivered_time = nullptr;
s_vpi_value* g_delivered_value = nullptr;
void* g_delivered_user_data = nullptr;
VpiHandle g_delivered_obj = nullptr;

int RecordDelivery(s_cb_data* data) {
  ++g_deliver_calls;
  g_delivered_ptr = data;
  if (data) {
    g_delivered_reason = data->reason;
    g_delivered_time = data->time;
    g_delivered_value = data->value;
    g_delivered_user_data = data->user_data;
    g_delivered_obj = VpiObjectOf(data->obj);
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
    watched_.type = vpiReg;
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
  // A variable to place a value change callback on where the case is about
  // the delivery rather than the object.
  VpiObject watched_;
};

// §38.36.1: a cbReclaimObj callback has no relationship to simulation time, so
// the time field passed to the routine is NULL - even though a time structure
// with a concrete type was supplied at registration.
TEST_F(VpiSimEventCbDelivery, ReclaimObjCallbackDeliveredWithoutTime) {
  s_vpi_time requested = {};
  requested.type = vpiSimTime;

  VpiObject class_object;
  class_object.type = vpiClassObj;
  s_cb_data cb = {};
  cb.reason = cbReclaimObj;
  cb.cb_rtn = &RecordDelivery;
  cb.obj = VpiHandleOf(&class_object);
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
  s_vpi_time requested = {};
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
// cbReclaimObj and cbEndOfObject. A different simulation-event reason that
// asked for a time is given one, in a structure that belongs to the simulator
// (§38.36) rather than the one the application registered.
TEST_F(VpiSimEventCbDelivery, ValueChangeCallbackKeepsRequestedTime) {
  s_vpi_time requested = {};
  requested.type = vpiSimTime;

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = &RecordDelivery;
  cb.obj = VpiHandleOf(&watched_);
  cb.time = &requested;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  int fired = vpi_ctx_.DispatchCallbacks(cbValueChange);

  EXPECT_EQ(fired, 1);
  EXPECT_NE(g_delivered_time, nullptr);
  EXPECT_NE(g_delivered_time, &requested);
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
  cb.obj = VpiHandleOf(&watched_);
  cb.user_data = reinterpret_cast<PLI_BYTE8*>(&payload);
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

// §38.36.1: a force the run reports with no statement the model holds an
// object for still calls a cbForce placed on no object, with no statement in
// obj and, there being no left-hand side to read, the value structure it was
// registered with as it was.
TEST_F(VpiSimEventCbDelivery, AForceWithNoStatementObjectStillCallsBack) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 7;
  s_cb_data cb = {};
  cb.reason = cbForce;
  cb.cb_rtn = &RecordDelivery;
  cb.value = &value;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  Variable forced{};
  vpi_ctx_.NoteForce(cbForce, &forced, nullptr, "");

  EXPECT_EQ(g_deliver_calls, 1);
  EXPECT_EQ(g_delivered_obj, nullptr);
  EXPECT_EQ(g_delivered_value, &value);
  EXPECT_EQ(value.value.integer, 7);
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
  cb.obj = VpiHandleOf(&disabled_task);
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  int fired = vpi_ctx_.DispatchCallbacks(cbDisable, &disabled_task);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_delivered_reason, cbDisable);
  EXPECT_EQ(g_delivered_obj, &disabled_task);
}

// §38.36.1 with §37.77: a disable the model holds no statement object for
// names no block or task the callback could be given, so a cbDisable is not
// called for it.
TEST_F(VpiSimEventCbDelivery, ADisableWithNoStatementObjectCallsNothing) {
  s_cb_data cb = {};
  cb.reason = cbDisable;
  cb.cb_rtn = &RecordDelivery;
  cb.obj = VpiHandleOf(&watched_);
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  Stmt disable{};
  disable.kind = StmtKind::kDisable;
  vpi_ctx_.NoteDisabled(&disable, "");

  EXPECT_EQ(g_deliver_calls, 0);
}

// §38.36.1: a cbReclaimObj placed on a class typespec is called as an object
// of that class is reclaimed, and not as an object of another class is.
TEST_F(VpiSimEventCbDelivery, AReclaimCallbackOnATypespecIsAboutItsClass) {
  VpiObject spec_c;
  spec_c.type = vpiClassTypespec;
  spec_c.name = "C";
  VpiObject spec_d;
  spec_d.type = vpiClassTypespec;
  spec_d.name = "D";
  VpiObject of_c;
  of_c.type = vpiClassObj;
  of_c.children.push_back(&spec_c);
  VpiObject of_d;
  of_d.type = vpiClassObj;
  of_d.children.push_back(&spec_d);

  s_cb_data cb = {};
  cb.reason = cbReclaimObj;
  cb.cb_rtn = &RecordDelivery;
  cb.obj = VpiHandleOf(&spec_c);
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  vpi_ctx_.ReleaseClassObject(&of_d);
  EXPECT_EQ(g_deliver_calls, 0);
  vpi_ctx_.ReleaseClassObject(&of_c);
  EXPECT_EQ(g_deliver_calls, 1);
  EXPECT_EQ(g_delivered_obj, &of_c);
}

// §38.36.1: a cbReclaimObj placed on a class object is called as that object
// is reclaimed, and not as another object of its class is.
TEST_F(VpiSimEventCbDelivery, AReclaimCallbackOnAnObjectIsAboutItAlone) {
  VpiObject spec;
  spec.type = vpiClassTypespec;
  spec.name = "C";
  VpiObject placed_on;
  placed_on.type = vpiClassObj;
  placed_on.children.push_back(&spec);
  VpiObject other;
  other.type = vpiClassObj;
  other.children.push_back(&spec);

  s_cb_data cb = {};
  cb.reason = cbReclaimObj;
  cb.cb_rtn = &RecordDelivery;
  cb.obj = VpiHandleOf(&placed_on);
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  vpi_ctx_.ReleaseClassObject(&other);
  EXPECT_EQ(g_deliver_calls, 0);
  vpi_ctx_.ReleaseClassObject(&placed_on);
  EXPECT_EQ(g_deliver_calls, 1);
}

// §38.36.1: a cbEndOfFrame, cbEndOfThread or cbEndOfObject placed on a frame, a
// thread or a transient object is called as that one ends, and not as another
// of its kind does.
TEST_F(VpiSimEventCbDelivery, AnEndCallbackIsAboutTheObjectItIsPlacedOn) {
  VpiObject frames[2];
  VpiObject threads[2];
  VpiObject objects[2];
  for (int i = 0; i < 2; ++i) {
    frames[i].type = vpiFrame;
    threads[i].type = vpiThread;
    objects[i].type = vpiClassObj;
  }
  for (const auto& [reason, on] : {std::pair{cbEndOfFrame, &frames[0]},
                                   std::pair{cbEndOfThread, &threads[0]},
                                   std::pair{cbEndOfObject, &objects[0]}}) {
    s_cb_data cb = {};
    cb.reason = reason;
    cb.cb_rtn = &RecordDelivery;
    cb.obj = VpiHandleOf(on);
    ASSERT_NE(vpi_register_cb(&cb), nullptr);
  }

  vpi_ctx_.ReleaseFrameOrThreadObject(&frames[1]);
  vpi_ctx_.ReleaseFrameOrThreadObject(&threads[1]);
  vpi_ctx_.ReleaseClassObject(&objects[1]);
  EXPECT_EQ(g_deliver_calls, 0);
  vpi_ctx_.ReleaseFrameOrThreadObject(&frames[0]);
  vpi_ctx_.ReleaseFrameOrThreadObject(&threads[0]);
  vpi_ctx_.ReleaseClassObject(&objects[0]);
  EXPECT_EQ(g_deliver_calls, 3);
}

// §38.36.1: a cbValueChange callback may be placed on an event statement. Since
// an event statement has no value, the value field the routine receives is
// NULL, even though a value structure was supplied at registration. Here the
// obj is the named-event object the trigger acts on.
TEST_F(VpiSimEventCbDelivery, ValueChangeOnNamedEventDeliversNullValue) {
  VpiObject named_event;
  named_event.type = vpiNamedEvent;
  s_vpi_value requested = {};

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = &RecordDelivery;
  cb.obj = VpiHandleOf(&named_event);
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
  s_vpi_value requested = {};

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = &RecordDelivery;
  cb.obj = VpiHandleOf(&event_stmt);
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
  s_vpi_value requested = {};

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = &RecordDelivery;
  cb.obj = VpiHandleOf(&class_var);
  cb.value = &requested;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  int fired = vpi_ctx_.DispatchCallbacks(cbValueChange, &class_var);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_delivered_value, nullptr);
}

// §38.36.1 (negative form of the value-is-NULL rule): the NULL-value delivery
// is specific to valueless/opaque objects. A cbValueChange callback on an
// ordinary declared variable that asked for a value is given one, in a
// structure that belongs to the simulator (§38.36).
TEST_F(VpiSimEventCbDelivery, ValueChangeOnOrdinaryVariableKeepsValue) {
  sim_ctx_.CreateVariable("ord", 1);
  vpi_ctx_.Attach(sim_ctx_);
  vpiHandle var = vpi_handle_by_name(VpiText("ord"), nullptr);
  ASSERT_NE(var, nullptr);
  s_vpi_value requested = {};

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = &RecordDelivery;
  cb.obj = var;
  cb.value = &requested;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  int fired = vpi_ctx_.DispatchCallbacks(cbValueChange, VpiObjectOf(var));

  EXPECT_EQ(fired, 1);
  EXPECT_NE(g_delivered_value, nullptr);
  EXPECT_NE(g_delivered_value, &requested);
}

constexpr const char* kValueChanges =
    "module top; timeunit 1ns; timeprecision 1ns; int x; int arr[4];\n"
    "  initial begin\n"
    "    $arm;\n"
    "    #1 x = 5;\n"
    "    #1 arr[2] = 8;\n"
    "    #1 x = 5;\n"
    "    #1 x = 6;\n"
    "  end\n"
    "endmodule\n";

void ArmValueChanges() {
  PlaceEventCallback(cbValueChange,
                     vpi_handle_by_name(VpiText("top.x"), nullptr));
  PlaceEventCallback(
      cbValueChange,
      vpi_handle_by_index(vpi_handle_by_name(VpiText("top.arr"), nullptr), 2));
}

// §38.36.1: a cbValueChange routine is called after each change of the value
// of the object it was placed on, a write of the value it holds being no
// change (#5106).
TEST_F(EventCallbacksOfARun, AValueChangeCallbackFiresOnEachChange) {
  Armer() = &ArmValueChanges;
  Run(kValueChanges);
  ASSERT_EQ(EventDeliveries().size(), 3u);
  EXPECT_EQ(EventDeliveries()[0].obj, "x");
  EXPECT_EQ(EventDeliveries()[1].obj, "arr[2]");
  EXPECT_EQ(EventDeliveries()[2].obj, "x");
}

// §38.36.1: the routine is given the current time and the object's new value
// in the forms the registration asked for, and, for an array member, the
// index of the member that changed (#5107).
TEST_F(EventCallbacksOfARun, AValueChangeCallbackIsGivenTheTimeValueAndIndex) {
  Armer() = &ArmValueChanges;
  Run(kValueChanges);
  ASSERT_EQ(EventDeliveries().size(), 3u);
  EXPECT_EQ(EventDeliveries()[0].value, 5);
  EXPECT_EQ(EventDeliveries()[0].time, 1u);
  EXPECT_EQ(EventDeliveries()[1].value, 8);
  EXPECT_EQ(EventDeliveries()[1].time, 2u);
  EXPECT_EQ(EventDeliveries()[1].index, 2);
  EXPECT_EQ(EventDeliveries()[2].value, 6);
  EXPECT_EQ(EventDeliveries()[2].time, 4u);
}

// §38.36.1 with §37.17 detail 14: a cbSizeChange routine is called after a
// queue is resized, with its new size as its value (#5121).
TEST_F(EventCallbacksOfARun, ASizeChangeCallbackFiresOnEachResize) {
  Armer() = [] { PlaceEventCallback(cbSizeChange, TopObject("top.q")); };
  Run("module top; timeunit 1ns; timeprecision 1ns; int q[$];\n"
      "  initial begin $arm;\n"
      "    #1 q.push_back(7); q.push_back(8); #1 void'(q.pop_front());\n"
      "  end\n"
      "endmodule\n");
  const std::vector<EventDelivery> kSizes = DeliveriesOf(cbSizeChange);
  ASSERT_EQ(kSizes.size(), 3u);
  EXPECT_EQ(kSizes[0].value, 1);
  EXPECT_EQ(kSizes[1].value, 2);
  EXPECT_EQ(kSizes[2].value, 1);
  EXPECT_EQ(kSizes[2].time, 2u);
}

// §38.36.1 with §37.17 detail 13: a cbValueChange routine placed on a bit of a
// vector is called after each change of that bit, and not after a write that
// changes only other bits of the vector (#7849).
TEST_F(EventCallbacksOfARun,
       AValueChangeCallbackOnABitFiresWhenThatBitChanges) {
  Armer() = [] {
    PlaceEventCallback(cbValueChange,
                       vpi_handle_by_index(TopObject("top.v"), 2));
  };
  Run("module top; timeunit 1ns; timeprecision 1ns; logic [3:0] v = 0;\n"
      "  initial begin $arm;\n"
      "    #1 v[0] = 1; #1 v[2] = 1; #1 v = 4'b0100; #1 v = 4'b0000;\n"
      "  end\n"
      "endmodule\n");
  const std::vector<EventDelivery> kChanges = DeliveriesOf(cbValueChange);
  ASSERT_EQ(kChanges.size(), 2u);
  EXPECT_EQ(kChanges[0].time, 2u);
  EXPECT_EQ(kChanges[1].time, 4u);
}

// §38.36.1: a resize calls the cbSizeChange routines placed on the queue it
// resizes and none placed elsewhere, a queue watched for value changes alone
// among them (#7849).
TEST_F(EventCallbacksOfARun, AResizeCallsOnlyTheSizeCallbacksOfItsQueue) {
  Armer() = [] {
    PlaceEventCallback(cbValueChange, TopObject("top.q"));
    PlaceEventCallback(cbSizeChange, TopObject("top.r"));
  };
  Run("module top; timeunit 1ns; timeprecision 1ns; int q[$]; int r[$];\n"
      "  initial begin $arm;\n"
      "    #1 q.push_back(7); #1 r.push_back(8);\n"
      "  end\n"
      "endmodule\n");
  const std::vector<EventDelivery> kSizes = DeliveriesOf(cbSizeChange);
  ASSERT_EQ(kSizes.size(), 1u);
  EXPECT_EQ(kSizes[0].obj, "r");
  EXPECT_EQ(kSizes[0].time, 2u);
}

// §38.36.1: cbStartOfThread is called whenever a thread is created, each
// branch of a fork among them (#5122).
TEST_F(EventCallbacksOfARun, AStartOfThreadCallbackFiresForEachForkBranch) {
  Armer() = [] { PlaceEventCallback(cbStartOfThread, nullptr); };
  Run("module top;\n"
      "  initial begin $arm; fork #1; #1; join end\n"
      "endmodule\n");
  EXPECT_EQ(DeliveriesOf(cbStartOfThread).size(), 2u);
}

// §38.36.1: a cbCreateObj placed on a class typespec is called once each
// constructor of an object of that type completes (#5123).
TEST_F(EventCallbacksOfARun, ACreateObjCallbackFiresForEachNew) {
  Armer() = [] {
    PlaceEventCallback(cbCreateObj,
                       vpi_handle(vpiTypespec, TopObject("top.c")));
  };
  Run("module top; class C; endclass C c;\n"
      "  initial begin $arm; c = new; c = new; c = new; end\n"
      "endmodule\n");
  EXPECT_EQ(DeliveriesOf(cbCreateObj).size(), 3u);
}

bool& BitPlacementRefused() {
  static bool refused = false;
  return refused;
}

// §38.36.1 with §37.17 detail 13: a cbForce, cbRelease or cbDisable may not
// be placed on a bit-select of a variable, which a var bit is (#5124).
TEST_F(EventCallbacksOfARun, AForceCallbackOnAVarBitIsRefused) {
  BitPlacementRefused() = false;
  Armer() = [] {
    vpiHandle bit = vpi_handle_by_index(TopObject("top.v"), 0);
    BitPlacementRefused() = PlaceEventCallback(cbForce, bit) == nullptr &&
                            vpi_chk_error(nullptr) != 0;
  };
  Run("module top; logic [3:0] v; initial $arm; endmodule\n");
  EXPECT_TRUE(BitPlacementRefused());
}

constexpr const char* kForceRelease =
    "module top; timeunit 1ns; timeprecision 1ns; int x;\n"
    "  initial begin $arm; #1 force x = 5; #1 release x; end\n"
    "endmodule\n";

// §38.36.1: a cbForce routine is called after a force of the object it was
// placed on, given the forced value (#5125).
TEST_F(EventCallbacksOfARun, AForceCallbackFiresAfterAForce) {
  Armer() = [] { PlaceEventCallback(cbForce, TopObject("top.x")); };
  Run(kForceRelease);
  const std::vector<EventDelivery> kForces = DeliveriesOf(cbForce);
  ASSERT_EQ(kForces.size(), 1u);
  EXPECT_EQ(kForces[0].value, 5);
  EXPECT_EQ(kForces[0].time, 1u);
}

// §38.36.1: a cbRelease routine is called after a release of the object it
// was placed on, given its value after the release (#5126).
TEST_F(EventCallbacksOfARun, AReleaseCallbackFiresAfterARelease) {
  Armer() = [] { PlaceEventCallback(cbRelease, TopObject("top.x")); };
  Run(kForceRelease);
  const std::vector<EventDelivery> kReleases = DeliveriesOf(cbRelease);
  ASSERT_EQ(kReleases.size(), 1u);
  EXPECT_EQ(kReleases[0].value, 5);
  EXPECT_EQ(kReleases[0].time, 2u);
}

// §38.36.1: a cbDisable routine is called after the named block it was
// placed on is disabled (#5127).
TEST_F(EventCallbacksOfARun, ADisableCallbackFiresWhenItsBlockIsDisabled) {
  Armer() = [] { PlaceEventCallback(cbDisable, TopObject("top.blk")); };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  initial $arm;\n"
      "  initial begin : blk #10 $noop; end\n"
      "  initial #3 disable blk;\n"
      "endmodule\n");
  const std::vector<EventDelivery> kDisables = DeliveriesOf(cbDisable);
  ASSERT_EQ(kDisables.size(), 1u);
  EXPECT_EQ(kDisables[0].obj, "blk");
  EXPECT_EQ(kDisables[0].time, 3u);
}

}  // namespace
}  // namespace delta
