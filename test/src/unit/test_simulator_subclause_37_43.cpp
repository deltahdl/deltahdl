#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(FrameModel, ActiveBooleanPropertyIsReported) {
  VpiContext ctx;

  VpiObject running;
  running.type = vpiFrame;
  running.active = true;
  EXPECT_EQ(ctx.Get(vpiActive, &running), 1);

  VpiObject suspended;
  suspended.type = vpiFrame;
  EXPECT_EQ(ctx.Get(vpiActive, &suspended), 0);
}

TEST(FrameModel, ParentRelationReachesTheActivatingFrame) {
  VpiObject parent;
  parent.type = vpiFrame;

  VpiObject child;
  child.type = vpiFrame;
  child.parent = &parent;

  EXPECT_EQ(VpiFrameParent(&child), &parent);
}

TEST(FrameModel, ParentRelationIsNullForRootAndNonFrameParents) {
  VpiObject root;
  root.type = vpiFrame;
  EXPECT_EQ(VpiFrameParent(&root), nullptr);

  EXPECT_EQ(VpiFrameParent(nullptr), nullptr);

  VpiObject thread_scope;
  thread_scope.type = vpiThread;
  VpiObject frame_in_thread;
  frame_in_thread.type = vpiFrame;
  frame_in_thread.parent = &thread_scope;
  EXPECT_EQ(VpiFrameParent(&frame_in_thread), nullptr);
}

TEST(FrameModel, OriginRelationReachesTheActivationPoint) {
  VpiObject call;
  call.type = vpiTaskCall;

  VpiObject frame;
  frame.type = vpiFrame;
  frame.frame_facts.origin = &call;
  EXPECT_EQ(VpiFrameOrigin(&frame), &call);

  VpiObject resolved_net;
  resolved_net.type = vpiNet;
  VpiObject resolution_frame;
  resolution_frame.type = vpiFrame;
  resolution_frame.frame_facts.origin = &resolved_net;
  EXPECT_EQ(VpiFrameOrigin(&resolution_frame), &resolved_net);

  VpiObject bare;
  bare.type = vpiFrame;
  bare.children = {&call};
  EXPECT_EQ(VpiFrameOrigin(&bare), nullptr);
  EXPECT_EQ(VpiFrameOrigin(nullptr), nullptr);
}

TEST(FrameModel, StmtTransitionReachesTheActiveStatement) {
  VpiObject stmt;
  stmt.type = vpiAssignment;

  VpiObject frame;
  frame.type = vpiFrame;
  frame.frame_facts.stmt = &stmt;
  EXPECT_EQ(VpiFrameStmt(&frame), &stmt);

  VpiObject bare;
  bare.type = vpiFrame;
  EXPECT_EQ(VpiFrameStmt(&bare), nullptr);
  EXPECT_EQ(VpiFrameStmt(nullptr), nullptr);
}

TEST(FrameModel, ThreadEdgeIsConsistentWithThreadFrameEdge) {
  VpiObject thread;
  thread.type = vpiThread;
  VpiObject frame;
  frame.type = vpiFrame;
  frame.active = true;

  thread.children = {&frame};
  frame.parent = &thread;

  EXPECT_EQ(VpiFrameThread(&frame), &thread);
  EXPECT_EQ(VpiThreadFrame(&thread), &frame);

  VpiObject bare;
  bare.type = vpiFrame;
  EXPECT_EQ(VpiFrameThread(&bare), nullptr);
  EXPECT_EQ(VpiFrameThread(nullptr), nullptr);
}

TEST(FrameModel, AutomaticsYieldLocalAutomaticObjects) {
  VpiObject stmt;
  stmt.type = vpiAssignment;
  VpiObject var;
  var.type = vpiLogicVar;
  var.automatic = true;
  VpiObject kept;
  kept.type = vpiIntVar;
  VpiObject ev;
  ev.type = vpiNamedEvent;
  ev.automatic = true;
  VpiObject ev_array;
  ev_array.type = vpiNamedEventArray;
  ev_array.automatic = true;

  VpiObject task;
  task.type = vpiTask;
  task.children = {&var, &stmt, &kept, &ev, &ev_array};
  VpiObject call;
  call.type = vpiTaskCall;
  call.tf_decl = &task;

  VpiObject frame;
  frame.type = vpiFrame;
  frame.frame_facts.origin = &call;

  std::vector<VpiHandle> automatics = VpiFrameAutomatics(&frame);
  ASSERT_EQ(automatics.size(), 3u);
  EXPECT_EQ(automatics[0], &var);
  EXPECT_EQ(automatics[1], &ev);
  EXPECT_EQ(automatics[2], &ev_array);
}

TEST(FrameModel, AutomaticsEmptyForNullAndNone) {
  VpiObject frame;
  frame.type = vpiFrame;
  EXPECT_TRUE(VpiFrameAutomatics(&frame).empty());
  VpiObject net;
  net.type = vpiNet;
  frame.frame_facts.origin = &net;
  EXPECT_TRUE(VpiFrameAutomatics(&frame).empty());
  EXPECT_TRUE(VpiFrameAutomatics(nullptr).empty());
}

TEST(FrameModel, AnotherRelationOrObjectIsNotTheFramesToResolve) {
  VpiObject frame;
  frame.type = vpiFrame;
  VpiObject before;
  VpiHandle out = &before;
  EXPECT_FALSE(VpiTryResolveFrameRelation(vpiScope, &frame, out));
  EXPECT_EQ(out, &before);

  VpiObject module;
  module.type = vpiModule;
  VpiObject iter;
  iter.type = vpiIterator;
  EXPECT_FALSE(VpiCollectFrameAutomatics(vpiAutomatics, &module, &iter));
  EXPECT_TRUE(iter.children.empty());
}

TEST(FrameModel, ActiveFrameReachedByNullFrameHandle) {
  VpiContext ctx;
  EXPECT_EQ(ctx.Handle(vpiFrame, nullptr), nullptr);

  VpiObject frame;
  frame.type = vpiFrame;
  ctx.SetActiveFrame(&frame);
  EXPECT_EQ(ctx.Handle(vpiFrame, nullptr), &frame);
  EXPECT_EQ(ctx.ActiveFrame(), &frame);
}

TEST(FrameModel, OnlyOneFrameIsActiveAtATime) {
  VpiContext ctx;

  VpiObject first;
  first.type = vpiFrame;
  VpiObject second;
  second.type = vpiFrame;

  ctx.SetActiveFrame(&first);
  ctx.SetActiveFrame(&second);

  EXPECT_EQ(ctx.Handle(vpiFrame, nullptr), &second);
}

TEST(FrameModel, ValueChangeCallbackOnAutomaticVariableIsRejected) {
  VpiContext ctx;

  VpiObject automatic_var;
  automatic_var.type = vpiLogicVar;
  automatic_var.automatic = true;
  s_cb_data on_automatic = {};
  on_automatic.reason = cbValueChange;
  on_automatic.obj = VpiHandleOf(&automatic_var);
  EXPECT_EQ(ctx.RegisterCb(&on_automatic), nullptr);
  EXPECT_EQ(ctx.LastError().level, kVpiError);

  VpiObject static_var;
  static_var.type = vpiLogicVar;
  s_cb_data on_static = {};
  on_static.reason = cbValueChange;
  on_static.obj = VpiHandleOf(&static_var);
  EXPECT_NE(ctx.RegisterCb(&on_static), nullptr);
}

class FrameSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

TEST_F(FrameSim, PutValueWithDelayOnAutomaticVariableIsRejected) {
  auto* var = sim_ctx_.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  VpiHandle h = vpi_ctx_.HandleByName("a", nullptr);
  ASSERT_NE(h, nullptr);
  h->automatic = true;

  s_vpi_value val = {};
  val.format = kVpiIntVal;
  val.value.integer = 55;
  s_vpi_time time = {};
  time.low = 10;
  vpi_ctx_.PutValue(h, &val, &time, vpiInertialDelay);

  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

TEST_F(FrameSim, PutValueWithoutDelayOnAutomaticVariableIsApplied) {
  auto* var = sim_ctx_.CreateVariable("b", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  VpiHandle h = vpi_ctx_.HandleByName("b", nullptr);
  ASSERT_NE(h, nullptr);
  h->automatic = true;

  s_vpi_value val = {};
  val.format = kVpiIntVal;
  val.value.integer = 55;
  vpi_ctx_.PutValue(h, &val, nullptr, vpiNoDelay);

  EXPECT_EQ(var->value.ToUint64(), 55u);
}

bool g_frame_found = false;
int g_frame_type = 0;
int g_frame_is_active = 0;
bool g_frame_has_a_thread = false;
bool g_frame_has_a_parent_frame = false;

PLI_INT32 InspectFrameCalltf(PLI_BYTE8*) {
  vpiHandle frame = vpi_handle(vpiFrame, nullptr);
  g_frame_found = frame != nullptr;
  if (frame == nullptr) return 0;
  g_frame_type = vpi_get(vpiType, frame);
  g_frame_is_active = vpi_get(vpiActive, frame);
  g_frame_has_a_thread = VpiFrameThread(VpiObjectOf(frame)) != nullptr;
  g_frame_has_a_parent_frame = VpiFrameParent(VpiObjectOf(frame)) != nullptr;
  return 0;
}

void RegisterFrameProbe() {
  g_frame_found = false;
  g_frame_type = 0;
  g_frame_is_active = 0;
  g_frame_has_a_thread = false;
  g_frame_has_a_parent_frame = false;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &InspectFrameCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

class FrameModelInARun : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(FrameModelInARun, TheActiveFrameIsTheSubroutineTheRunIsInside) {
  RegisterFrameProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  function automatic int one();\n"
      "    $probe;\n"
      "    return 1;\n"
      "  endfunction\n"
      "  initial r = one();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  ASSERT_TRUE(g_frame_found);
  EXPECT_EQ(g_frame_type, vpiFrame);
  EXPECT_EQ(g_frame_is_active, 1);
  EXPECT_TRUE(g_frame_has_a_thread);
  EXPECT_FALSE(g_frame_has_a_parent_frame);
}

TEST_F(FrameModelInARun, AFrameActivatedFromAnotherReportsItAsItsParent) {
  RegisterFrameProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  function automatic int inner();\n"
      "    $probe;\n"
      "    return 1;\n"
      "  endfunction\n"
      "  function automatic int outer();\n"
      "    return inner();\n"
      "  endfunction\n"
      "  initial r = outer();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  ASSERT_TRUE(g_frame_found);
  EXPECT_EQ(g_frame_is_active, 1);
  EXPECT_TRUE(g_frame_has_a_parent_frame);
  EXPECT_TRUE(g_frame_has_a_thread);
}

TEST_F(FrameModelInARun, ATaskEnableActivatesAFrame) {
  RegisterFrameProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  task automatic tk();\n"
      "    $probe;\n"
      "  endtask\n"
      "  initial tk();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  ASSERT_TRUE(g_frame_found);
  EXPECT_EQ(g_frame_is_active, 1);
  EXPECT_TRUE(g_frame_has_a_thread);
  EXPECT_FALSE(g_frame_has_a_parent_frame);
}

TEST_F(FrameModelInARun, AnotherThreadsTaskFrameIsNoParent) {
  RegisterFrameProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  task automatic wait_for(input int n);\n"
      "    #n;\n"
      "  endtask\n"
      "  function automatic int one();\n"
      "    $probe;\n"
      "    return 1;\n"
      "  endfunction\n"
      "  initial wait_for(5);\n"
      "  initial #1 r = one();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  ASSERT_TRUE(g_frame_found);
  EXPECT_FALSE(g_frame_has_a_parent_frame);
}

int g_frames_started = 0;
int g_frames_ended = 0;

PLI_INT32 CountFrameCallback(p_cb_data data) {
  if (data->reason == cbStartOfFrame) ++g_frames_started;
  if (data->reason == cbEndOfFrame) ++g_frames_ended;
  return 0;
}

TEST_F(FrameModelInARun, EachTaskEnableStartsAndEndsAFrame) {
  g_frames_started = 0;
  g_frames_ended = 0;
  for (int reason : {cbStartOfFrame, cbEndOfFrame}) {
    s_cb_data data = {};
    data.reason = reason;
    data.cb_rtn = &CountFrameCallback;
    ASSERT_NE(vpi_register_cb(&data), nullptr);
  }

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  task automatic wait_for(input int n);\n"
      "    #n;\n"
      "  endtask\n"
      "  initial begin wait_for(1); wait_for(2); wait_for(3); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_frames_started, 3);
  EXPECT_EQ(g_frames_ended, 3);
}

TEST(FrameModel, AFrameBelowNoThreadHasNone) {
  VpiObject thread;
  thread.type = vpiThread;
  VpiObject module;
  module.type = vpiModule;
  VpiObject outer;
  outer.type = vpiFrame;
  outer.parent = &module;
  VpiObject frame;
  frame.type = vpiFrame;
  frame.parent = &outer;
  frame.children = {&thread};
  EXPECT_EQ(VpiFrameThread(&frame), nullptr);
}

struct FrameSeen {
  bool found = false;
  int origin_type = 0;
  std::string origin_callee;
  bool stmt_is_the_call = false;
  std::vector<std::string> automatics;
  int parent_type = 0;
  bool parent_stmt_is_origin = false;
  bool thread_found = false;
  bool parent_shares_thread = false;
};
FrameSeen g_seen;

std::string CalleeName(vpiHandle call) {
  vpiHandle callee = vpi_handle(vpiTask, call);
  if (callee == nullptr) callee = vpi_handle(vpiFunction, call);
  return callee == nullptr ? "" : vpi_get_str(vpiName, callee);
}

PLI_INT32 LookAtFrameCalltf(PLI_BYTE8*) {
  g_seen = {};
  vpiHandle frame = vpi_handle(vpiFrame, nullptr);
  if (frame == nullptr) return 0;
  g_seen.found = true;
  vpiHandle origin = vpi_handle(vpiOrigin, frame);
  if (origin != nullptr) {
    g_seen.origin_type = vpi_get(vpiType, origin);
    g_seen.origin_callee = CalleeName(origin);
  }
  g_seen.stmt_is_the_call =
      vpi_compare_objects(vpi_handle(vpiStmt, frame),
                          vpi_handle(vpiSysTfCall, nullptr)) != 0;
  vpiHandle it = vpi_iterate(vpiAutomatics, frame);
  while (vpiHandle object = it == nullptr ? nullptr : vpi_scan(it)) {
    g_seen.automatics.emplace_back(vpi_get_str(vpiName, object));
  }
  vpiHandle thread = vpi_handle(vpiThread, frame);
  g_seen.thread_found = thread != nullptr;
  vpiHandle parent = vpi_handle(vpiParent, frame);
  if (parent == nullptr) return 0;
  g_seen.parent_type = vpi_get(vpiType, parent);
  g_seen.parent_stmt_is_origin =
      origin != nullptr &&
      vpi_compare_objects(vpi_handle(vpiStmt, parent), origin) != 0;
  g_seen.parent_shares_thread =
      thread != nullptr &&
      vpi_compare_objects(vpi_handle(vpiThread, parent), thread) != 0;
  return 0;
}

void RegisterFrameLook() {
  g_seen = {};
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$look");
  data.calltf = &LookAtFrameCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

TEST_F(FrameModelInARun, ATaskFrameReachesItsCallStatementAndAutomatics) {
  RegisterFrameLook();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  task automatic tk();\n"
      "    int x;\n"
      "    static int s;\n"
      "    logic [3:0] y;\n"
      "    event e;\n"
      "    $look;\n"
      "  endtask\n"
      "  initial tk();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  ASSERT_TRUE(g_seen.found);
  EXPECT_EQ(g_seen.origin_type, vpiTaskCall);
  EXPECT_EQ(g_seen.origin_callee, "tk");
  EXPECT_TRUE(g_seen.stmt_is_the_call);
  EXPECT_EQ(g_seen.automatics, (std::vector<std::string>{"x", "y", "e"}));
  EXPECT_TRUE(g_seen.thread_found);
  EXPECT_EQ(g_seen.parent_type, 0);
}

TEST_F(FrameModelInARun, AFunctionFrameReachesTheCallInItsExpression) {
  RegisterFrameLook();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  function automatic int one();\n"
      "    $look;\n"
      "    return 1;\n"
      "  endfunction\n"
      "  initial r = 2 + one();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  ASSERT_TRUE(g_seen.found);
  EXPECT_EQ(g_seen.origin_type, vpiFuncCall);
  EXPECT_EQ(g_seen.origin_callee, "one");
}

TEST_F(FrameModelInARun, ANestedFrameReachesItsParentAndTheirThread) {
  RegisterFrameLook();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  task automatic inner();\n"
      "    $look;\n"
      "  endtask\n"
      "  task automatic outer();\n"
      "    #1;\n"
      "    inner();\n"
      "  endtask\n"
      "  initial outer();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  ASSERT_TRUE(g_seen.found);
  EXPECT_EQ(g_seen.origin_callee, "inner");
  EXPECT_EQ(g_seen.parent_type, vpiFrame);
  EXPECT_TRUE(g_seen.parent_stmt_is_origin);
  EXPECT_TRUE(g_seen.thread_found);
  EXPECT_TRUE(g_seen.parent_shares_thread);
}

int g_x_automatic = -1;
int g_s_automatic = -1;
int g_z_automatic = -1;
bool g_x_callback_placed = true;

PLI_INT32 NoValueChange(p_cb_data) { return 0; }

int AutomaticOf(const char* name) {
  vpiHandle var = vpi_handle_by_name(VpiText(name), nullptr);
  return var == nullptr ? -1 : vpi_get(vpiAutomatic, var);
}

PLI_INT32 LookAtLifetimesCalltf(PLI_BYTE8*) {
  g_x_automatic = AutomaticOf("t.b.x");
  g_s_automatic = AutomaticOf("t.b.s");
  g_z_automatic = AutomaticOf("t.tk.c.z");
  s_vpi_time time = {};
  time.type = vpiSimTime;
  s_vpi_value value = {};
  value.format = vpiIntVal;
  s_cb_data data = {};
  data.reason = cbValueChange;
  data.cb_rtn = &NoValueChange;
  data.obj = vpi_handle_by_name(VpiText("t.b.x"), nullptr);
  data.time = &time;
  data.value = &value;
  g_x_callback_placed =
      data.obj == nullptr || vpi_register_cb(&data) != nullptr;
  return 0;
}

TEST_F(FrameModelInARun, ABlocksAutomaticVariablesAreAutomatic) {
  g_x_automatic = g_s_automatic = g_z_automatic = -1;
  g_x_callback_placed = true;
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$lifetimes");
  data.calltf = &LookAtLifetimesCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  task automatic tk();\n"
      "    begin : c\n"
      "      int z;\n"
      "      z = 1;\n"
      "    end\n"
      "  endtask\n"
      "  initial begin : b\n"
      "    automatic int x;\n"
      "    static int s;\n"
      "    $lifetimes;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_x_automatic, 1);
  EXPECT_EQ(g_s_automatic, 0);
  EXPECT_EQ(g_z_automatic, 1);
  EXPECT_FALSE(g_x_callback_placed);
}

}  // namespace
}  // namespace delta
