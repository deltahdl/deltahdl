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

class VpiSimEventCb : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

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

TEST_F(VpiSimEventCb, ForceAndReleaseCallbacksOnNoObjectAccepted) {
  for (int reason : {cbForce, cbRelease}) {
    s_cb_data cb = {};
    cb.reason = reason;
    EXPECT_NE(vpi_register_cb(&cb), nullptr) << "reason " << reason;
  }
}

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

TEST_F(VpiSimEventCb, ForceCallbackWithNullObjectAccepted) {
  s_cb_data cb = {};
  cb.reason = cbForce;
  cb.obj = nullptr;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

TEST_F(VpiSimEventCb, ValueChangeCallbackOnBitSelectAccepted) {
  vpiHandle bit = MakeBitSelectHandle("v");
  ASSERT_NE(bit, nullptr);

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = bit;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

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
  VpiObject watched_;
};

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
  EXPECT_EQ(g_delivered_time, nullptr);
}

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
  EXPECT_NE(g_delivered_ptr, &cb);
  EXPECT_EQ(g_delivered_user_data, &payload);
}

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

TEST_F(EventCallbacksOfARun, AValueChangeCallbackFiresOnEachChange) {
  Armer() = &ArmValueChanges;
  Run(kValueChanges);
  ASSERT_EQ(EventDeliveries().size(), 3u);
  EXPECT_EQ(EventDeliveries()[0].obj, "x");
  EXPECT_EQ(EventDeliveries()[1].obj, "arr[2]");
  EXPECT_EQ(EventDeliveries()[2].obj, "x");
}

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

TEST_F(EventCallbacksOfARun, AStartOfThreadCallbackFiresForEachForkBranch) {
  Armer() = [] { PlaceEventCallback(cbStartOfThread, nullptr); };
  Run("module top;\n"
      "  initial begin $arm; fork #1; #1; join end\n"
      "endmodule\n");
  EXPECT_EQ(DeliveriesOf(cbStartOfThread).size(), 2u);
}

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

TEST_F(EventCallbacksOfARun, AForceCallbackFiresAfterAForce) {
  Armer() = [] { PlaceEventCallback(cbForce, TopObject("top.x")); };
  Run(kForceRelease);
  const std::vector<EventDelivery> kForces = DeliveriesOf(cbForce);
  ASSERT_EQ(kForces.size(), 1u);
  EXPECT_EQ(kForces[0].value, 5);
  EXPECT_EQ(kForces[0].time, 1u);
}

TEST_F(EventCallbacksOfARun, AReleaseCallbackFiresAfterARelease) {
  Armer() = [] { PlaceEventCallback(cbRelease, TopObject("top.x")); };
  Run(kForceRelease);
  const std::vector<EventDelivery> kReleases = DeliveriesOf(cbRelease);
  ASSERT_EQ(kReleases.size(), 1u);
  EXPECT_EQ(kReleases[0].value, 5);
  EXPECT_EQ(kReleases[0].time, 2u);
}

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
