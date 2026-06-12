#include <gtest/gtest.h>

#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.43 frame: the VPI object model for a frame - any dynamically activated
// procedural scope, together with its locally declared automatic variables,
// events, and event arrays, if any (detail 1). The diagram gives a frame one
// Boolean property (vpiActive) and several relations: vpiParent reaches the
// frame that activated it, vpiOrigin reaches the elaboration-hierarchy point it
// was activated from, the frame-to-stmt transition reaches the active statement
// within it, the frame--thread edge reaches the thread it belongs to, and
// vpiAutomatics iterates the automatic objects it declares. These tests observe
// the production helpers in vpi.cpp and VpiContext (Get, Handle, RegisterCb,
// PutValue) applying those rules.
//
// vpiActive and the frame--thread edge are shared with §37.44 (Threads): the
// same Boolean property and the same diagram edge, woven so a frame and a thread
// report activeness identically and reach each other consistently.

// detail 1 (vpiActive, shared with §37.44): a frame reports whether it is the
// active one through vpi_get(vpiActive), the same property a thread reports.
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

// detail 5 (vpiParent -> frame): a frame reaches the frame from which it was
// activated through its parent link.
TEST(FrameModel, ParentRelationReachesTheActivatingFrame) {
  VpiObject parent;
  parent.type = vpiFrame;

  VpiObject child;
  child.type = vpiFrame;
  child.parent = &parent;

  EXPECT_EQ(VpiFrameParent(&child), &parent);
}

// detail 5 edge: a root frame (no parent) and a null handle report no parent; a
// parent that is not a frame is not reported as a frame parent.
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

// detail 6 (vpiOrigin): a frame reaches the elaboration-hierarchy point it was
// activated from. The net case covers a frame activated for a nettype's
// user-defined resolution function. None is reported when no origin is attached.
TEST(FrameModel, OriginRelationReachesTheActivationPoint) {
  VpiObject scope;
  scope.type = vpiScope;

  VpiObject frame;
  frame.type = vpiFrame;
  frame.children = {&scope};
  EXPECT_EQ(VpiFrameOrigin(&frame), &scope);

  VpiObject resolved_net;
  resolved_net.type = vpiNet;
  VpiObject resolution_frame;
  resolution_frame.type = vpiFrame;
  resolution_frame.children = {&resolved_net};
  EXPECT_EQ(VpiFrameOrigin(&resolution_frame), &resolved_net);

  VpiObject bare;
  bare.type = vpiFrame;
  EXPECT_EQ(VpiFrameOrigin(&bare), nullptr);
  EXPECT_EQ(VpiFrameOrigin(nullptr), nullptr);
}

// detail 6: the origin kinds the diagram draws - a scope, a task or function
// call (including the system and method forms), or a net or net array - are
// accepted as frame origins; a plain statement is not an origin.
TEST(FrameModel, OriginKindsCoverScopesCallsAndNets) {
  EXPECT_TRUE(VpiIsFrameOriginType(vpiScope));
  EXPECT_TRUE(VpiIsFrameOriginType(vpiTaskCall));
  EXPECT_TRUE(VpiIsFrameOriginType(vpiFuncCall));
  EXPECT_TRUE(VpiIsFrameOriginType(vpiSysTaskCall));
  EXPECT_TRUE(VpiIsFrameOriginType(vpiSysFuncCall));
  EXPECT_TRUE(VpiIsFrameOriginType(vpiMethodTaskCall));
  EXPECT_TRUE(VpiIsFrameOriginType(vpiMethodFuncCall));
  EXPECT_TRUE(VpiIsFrameOriginType(vpiNet));
  EXPECT_TRUE(VpiIsFrameOriginType(vpiNetArray));

  EXPECT_FALSE(VpiIsFrameOriginType(vpiStmt));
  EXPECT_FALSE(VpiIsFrameOriginType(vpiThread));
}

// details 4 and 5 (frame-to-stmt transition): a frame reaches the active
// statement within it (for a parent frame, the statement whose execution
// activated the child frame). None is reported when no statement is attached.
TEST(FrameModel, StmtTransitionReachesTheActiveStatement) {
  VpiObject stmt;
  stmt.type = vpiStmt;

  VpiObject frame;
  frame.type = vpiFrame;
  frame.children = {&stmt};
  EXPECT_EQ(VpiFrameStmt(&frame), &stmt);

  VpiObject bare;
  bare.type = vpiFrame;
  EXPECT_EQ(VpiFrameStmt(&bare), nullptr);
  EXPECT_EQ(VpiFrameStmt(nullptr), nullptr);
}

// frame--thread edge (shared with §37.44): a frame reaches the thread it belongs
// to, and §37.44's VpiThreadFrame reaches that frame back from the thread - the
// two directions of the same diagram edge agree on the same pair.
TEST(FrameModel, ThreadEdgeIsConsistentWithThreadFrameEdge) {
  VpiObject thread;
  thread.type = vpiThread;
  VpiObject frame;
  frame.type = vpiFrame;

  thread.children = {&frame};
  frame.children = {&thread};

  EXPECT_EQ(VpiFrameThread(&frame), &thread);
  EXPECT_EQ(VpiThreadFrame(&thread), &frame);

  VpiObject bare;
  bare.type = vpiFrame;
  EXPECT_EQ(VpiFrameThread(&bare), nullptr);
  EXPECT_EQ(VpiFrameThread(nullptr), nullptr);
}

// detail 1 (vpiAutomatics): the iteration yields the frame's locally declared
// automatic objects - its automatic variables, named events, and named event
// arrays - in order, skipping the frame's origin scope and active statement.
TEST(FrameModel, AutomaticsYieldLocalAutomaticObjects) {
  VpiObject scope;
  scope.type = vpiScope;
  VpiObject stmt;
  stmt.type = vpiStmt;
  VpiObject var;
  var.type = vpiLogicVar;
  VpiObject ev;
  ev.type = vpiNamedEvent;
  VpiObject ev_array;
  ev_array.type = vpiNamedEventArray;

  VpiObject frame;
  frame.type = vpiFrame;
  frame.children = {&scope, &var, &stmt, &ev, &ev_array};

  std::vector<VpiHandle> automatics = VpiFrameAutomatics(&frame);
  ASSERT_EQ(automatics.size(), 3u);
  EXPECT_EQ(automatics[0], &var);
  EXPECT_EQ(automatics[1], &ev);
  EXPECT_EQ(automatics[2], &ev_array);
}

// detail 1 edge: a frame that declares no automatic objects, and a null handle,
// iterate to none.
TEST(FrameModel, AutomaticsEmptyForNullAndNone) {
  VpiObject frame;
  frame.type = vpiFrame;
  EXPECT_TRUE(VpiFrameAutomatics(&frame).empty());
  EXPECT_TRUE(VpiFrameAutomatics(nullptr).empty());
}

// detail 4: there is at most one active frame at a time in a given thread, and
// an application reaches it with vpi_handle(vpiFrame, NULL). Before any frame is
// made active, that query reports none.
TEST(FrameModel, ActiveFrameReachedByNullFrameHandle) {
  VpiContext ctx;
  EXPECT_EQ(ctx.Handle(vpiFrame, nullptr), nullptr);

  VpiObject frame;
  frame.type = vpiFrame;
  ctx.SetActiveFrame(&frame);
  EXPECT_EQ(ctx.Handle(vpiFrame, nullptr), &frame);
  EXPECT_EQ(ctx.ActiveFrame(), &frame);
}

// detail 4 (at most one active frame at a time): activating a second frame
// replaces the first, so vpi_handle(vpiFrame, NULL) reaches only the latest
// active frame - never two at once.
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

// detail 2: it is illegal to place a value change callback on an automatic
// variable; the registration is rejected. The same callback on a non-automatic
// variable is accepted.
TEST(FrameModel, ValueChangeCallbackOnAutomaticVariableIsRejected) {
  VpiContext ctx;

  VpiObject automatic_var;
  automatic_var.type = vpiLogicVar;
  automatic_var.automatic = true;
  VpiCbData on_automatic = {};
  on_automatic.reason = cbValueChange;
  on_automatic.obj = &automatic_var;
  EXPECT_EQ(ctx.RegisterCb(&on_automatic), nullptr);
  EXPECT_EQ(ctx.LastError().level, kVpiError);

  VpiObject static_var;
  static_var.type = vpiLogicVar;
  VpiCbData on_static = {};
  on_static.reason = cbValueChange;
  on_static.obj = &static_var;
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

// detail 3: it is illegal to put a value with a delay on an automatic variable;
// the put is rejected and the variable keeps its value.
TEST_F(FrameSim, PutValueWithDelayOnAutomaticVariableIsRejected) {
  auto* var = sim_ctx_.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  VpiHandle h = vpi_ctx_.HandleByName("a", nullptr);
  ASSERT_NE(h, nullptr);
  h->automatic = true;

  VpiValue val = {};
  val.format = kVpiIntVal;
  val.value.integer = 55;
  VpiTime time = {};
  time.low = 10;
  vpi_ctx_.PutValue(h, &val, &time, vpiInertialDelay);

  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

// detail 3 (rule is delay-specific): the same put without a delay on the same
// automatic variable is applied normally.
TEST_F(FrameSim, PutValueWithoutDelayOnAutomaticVariableIsApplied) {
  auto* var = sim_ctx_.CreateVariable("b", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  VpiHandle h = vpi_ctx_.HandleByName("b", nullptr);
  ASSERT_NE(h, nullptr);
  h->automatic = true;

  VpiValue val = {};
  val.format = kVpiIntVal;
  val.value.integer = 55;
  vpi_ctx_.PutValue(h, &val, nullptr, vpiNoDelay);

  EXPECT_EQ(var->value.ToUint64(), 55u);
}

}  // namespace
}  // namespace delta
