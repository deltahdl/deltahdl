#include <gtest/gtest.h>

#include <cstdint>
#include <functional>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_vpi_run.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

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
  s_vpi_time requested = {};
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
// cbReclaimObj and cbEndOfObject. A different simulation-event reason keeps the
// time structure the application requested, so the routine still sees it.
TEST_F(VpiSimEventCbDelivery, ValueChangeCallbackKeepsRequestedTime) {
  s_vpi_time requested = {};
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
  s_vpi_value requested = {};

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
  s_vpi_value requested = {};

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
  s_vpi_value requested = {};

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
  vpiHandle var = vpi_handle_by_name(VpiText("ord"), nullptr);
  ASSERT_NE(var, nullptr);
  s_vpi_value requested = {};

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = &RecordDelivery;
  cb.value = &requested;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  int fired = vpi_ctx_.DispatchCallbacks(cbValueChange, VpiObjectOf(var));

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_delivered_value, &requested);
}

// One delivery of a simulation-event callback as its routine saw it: the
// reason, the name of the object in its obj field, the value and the time it
// was given, and its index.
struct EventDelivery {
  int reason = 0;
  std::string obj;
  int value = 0;
  uint32_t time = 0;
  int index = 0;
  bool operator==(const EventDelivery&) const = default;
};

std::vector<EventDelivery>& EventDeliveries() {
  static std::vector<EventDelivery> deliveries;
  return deliveries;
}

// What `$arm` does when the design calls it.
std::function<void()>& Armer() {
  static std::function<void()> armer;
  return armer;
}

PLI_INT32 RecordEventDelivery(p_cb_data cb) {
  EventDelivery d;
  d.reason = cb->reason;
  const char* name =
      cb->obj != nullptr ? vpi_get_str(vpiName, cb->obj) : nullptr;
  d.obj = name == nullptr ? "" : name;
  d.value = cb->value != nullptr ? cb->value->value.integer : 0;
  d.time = cb->time != nullptr ? cb->time->low : 0;
  d.index = cb->index;
  EventDeliveries().push_back(d);
  return 0;
}

// Places a `reason` callback on `obj`, asking for the time as vpiSimTime
// and the value as vpiIntVal.
vpiHandle PlaceEventCallback(int reason, vpiHandle obj) {
  static s_vpi_time time;
  static s_vpi_value value;
  time.type = vpiSimTime;
  value.format = vpiIntVal;
  s_cb_data data = {};
  data.reason = reason;
  data.cb_rtn = &RecordEventDelivery;
  data.obj = obj;
  data.time = &time;
  data.value = &value;
  return vpi_register_cb(&data);
}

// A run whose design calls `$arm`, which places the case's callbacks once
// the model exists, its deliveries recorded.
class EventCallbacksOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    EventDeliveries().clear();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$arm");
    data.calltf = [](PLI_BYTE8*) -> PLI_INT32 {
      Armer()();
      return 0;
    };
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }
};

constexpr const char* kValueChanges =
    "`timescale 1ns/1ns\n"
    "module top; int x; int arr[4];\n"
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

// The deliveries recorded for `reason`, in order.
std::vector<EventDelivery> DeliveriesOf(int reason) {
  std::vector<EventDelivery> of;
  for (const EventDelivery& d : EventDeliveries()) {
    if (d.reason == reason) of.push_back(d);
  }
  return of;
}

vpiHandle TopObject(const char* name) {
  return vpi_handle_by_name(VpiText(name), nullptr);
}

// §38.36.1 with §37.17 detail 14: a cbSizeChange routine is called after a
// queue is resized, with its new size as its value (#5121).
TEST_F(EventCallbacksOfARun, ASizeChangeCallbackFiresOnEachResize) {
  Armer() = [] { PlaceEventCallback(cbSizeChange, TopObject("top.q")); };
  Run("`timescale 1ns/1ns\n"
      "module top; int q[$];\n"
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
    "`timescale 1ns/1ns\n"
    "module top; int x;\n"
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
  Run("`timescale 1ns/1ns\n"
      "module top;\n"
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
