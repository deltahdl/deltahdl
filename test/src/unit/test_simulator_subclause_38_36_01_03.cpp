#include <gtest/gtest.h>

#include <algorithm>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_simulator.h"
#include "helpers_sealed_design_run.h"
#include "helpers_stmt_callbacks.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

int g_calls = 0;
std::vector<VpiHandle> g_objs;

int RecordCb(s_cb_data* data) {
  ++g_calls;
  if (data) g_objs.push_back(VpiObjectOf(data->obj));
  return 0;
}

bool Fired(VpiHandle stmt) {
  return std::find(g_objs.begin(), g_objs.end(), stmt) != g_objs.end();
}

class VpiModuleWideCallback : public ::testing::Test {
 protected:
  void SetUp() override {
    g_calls = 0;
    g_objs.clear();
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiHandle AddStmt(VpiHandle module, const char* name, int type,
                    bool protect = false) {
    VpiHandle h = vpi_ctx_.CreateModule(name, name);
    h->type = type;
    h->is_protected = protect;
    module->children.push_back(h);
    return h;
  }

  vpiHandle RegisterModuleWide(VpiHandle module) {
    s_cb_data cb = {};
    cb.reason = cbStmt;
    cb.obj = VpiHandleOf(module);
    cb.cb_rtn = &RecordCb;
    return vpi_register_cb(&cb);
  }

  vpiHandle RegisterOnStatement(VpiHandle stmt) {
    s_cb_data cb = {};
    cb.reason = cbStmt;
    cb.obj = VpiHandleOf(stmt);
    cb.cb_rtn = &RecordCb;
    return vpi_register_cb(&cb);
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

TEST_F(VpiModuleWideCallback, PlacesCallbackOnEveryStatementIncludingNested) {
  VpiHandle module = vpi_ctx_.CreateModule("m", "m");
  VpiHandle flat = AddStmt(module, "m.a", vpiAssignment);
  VpiHandle block = AddStmt(module, "m.blk", vpiNamedBegin);
  VpiHandle nested = AddStmt(block, "m.blk.s", vpiWhile);

  ASSERT_NE(RegisterModuleWide(module), nullptr);
  vpi_ctx_.DispatchCallbacks(cbStmt);

  EXPECT_EQ(g_calls, 3);
  EXPECT_TRUE(Fired(flat));
  EXPECT_TRUE(Fired(block));
  EXPECT_TRUE(Fired(nested));
  EXPECT_FALSE(Fired(module));
}

TEST_F(VpiModuleWideCallback, NonStatementChildrenGetNoCallback) {
  VpiHandle module = vpi_ctx_.CreateModule("m", "m");
  VpiHandle stmt = AddStmt(module, "m.s", vpiAssignment);
  VpiHandle net = AddStmt(module, "m.n", vpiNet);

  ASSERT_NE(RegisterModuleWide(module), nullptr);
  vpi_ctx_.DispatchCallbacks(cbStmt);

  EXPECT_EQ(g_calls, 1);
  EXPECT_TRUE(Fired(stmt));
  EXPECT_FALSE(Fired(net));
}

TEST_F(VpiModuleWideCallback, ProtectedStatementsGetNoCallback) {
  VpiHandle module = vpi_ctx_.CreateModule("m", "m");
  VpiHandle open = AddStmt(module, "m.open", vpiAssignment, false);
  VpiHandle sealed = AddStmt(module, "m.sealed", vpiWhile, true);

  ASSERT_NE(RegisterModuleWide(module), nullptr);
  vpi_ctx_.DispatchCallbacks(cbStmt);

  EXPECT_EQ(g_calls, 1);
  EXPECT_TRUE(Fired(open));
  EXPECT_FALSE(Fired(sealed));
}

TEST_F(VpiModuleWideCallback, NestedModuleInstanceIsNotReached) {
  VpiHandle module = vpi_ctx_.CreateModule("m", "m");
  VpiHandle own = AddStmt(module, "m.s", vpiAssignment);
  VpiHandle sub = vpi_ctx_.CreateModule("m.sub", "m.sub");
  module->children.push_back(sub);
  VpiHandle sub_stmt = AddStmt(sub, "m.sub.s", vpiAssignment);

  ASSERT_NE(RegisterModuleWide(module), nullptr);
  vpi_ctx_.DispatchCallbacks(cbStmt);

  EXPECT_EQ(g_calls, 1);
  EXPECT_TRUE(Fired(own));
  EXPECT_FALSE(Fired(sub_stmt));
}

TEST_F(VpiModuleWideCallback, ModuleWithNoStatementsFiresNothing) {
  VpiHandle module = vpi_ctx_.CreateModule("m", "m");

  ASSERT_NE(RegisterModuleWide(module), nullptr);
  vpi_ctx_.DispatchCallbacks(cbStmt);

  EXPECT_EQ(g_calls, 0);
  EXPECT_FALSE(Fired(module));
}

TEST_F(VpiModuleWideCallback, SingleHandleRemovesCallbackFromEveryStatement) {
  VpiHandle module = vpi_ctx_.CreateModule("m", "m");
  AddStmt(module, "m.a", vpiAssignment);
  AddStmt(module, "m.b", vpiWhile);

  vpiHandle cb = RegisterModuleWide(module);
  ASSERT_NE(cb, nullptr);

  vpi_ctx_.DispatchCallbacks(cbStmt);
  EXPECT_EQ(g_calls, 2);

  EXPECT_EQ(vpi_ctx_.RemoveCb(VpiObjectOf(cb)), 1);
  g_calls = 0;
  g_objs.clear();
  vpi_ctx_.DispatchCallbacks(cbStmt);
  EXPECT_EQ(g_calls, 0);
}

TEST_F(VpiModuleWideCallback,
       StatementAboutToExecuteGetsTheCallbackPlacedOnIt) {
  VpiHandle module = vpi_ctx_.CreateModule("m", "m");
  VpiHandle first = AddStmt(module, "m.a", vpiAssignment);
  AddStmt(module, "m.b", vpiWhile);

  ASSERT_NE(RegisterModuleWide(module), nullptr);
  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbStmt, first), 1);

  EXPECT_EQ(g_calls, 1);
  EXPECT_TRUE(Fired(first));
  EXPECT_FALSE(Fired(module));
}

TEST_F(VpiModuleWideCallback, StatementOfAnotherInstanceCallsNothing) {
  VpiHandle module = vpi_ctx_.CreateModule("m", "m");
  AddStmt(module, "m.s", vpiAssignment);
  VpiHandle other = vpi_ctx_.CreateModule("n", "n");
  VpiHandle outside = AddStmt(other, "n.s", vpiAssignment);

  ASSERT_NE(RegisterModuleWide(module), nullptr);
  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbStmt, outside), 0);

  EXPECT_EQ(g_calls, 0);
  EXPECT_FALSE(Fired(outside));
}

TEST_F(VpiModuleWideCallback, ProtectedStatementAboutToExecuteCallsNothing) {
  VpiHandle module = vpi_ctx_.CreateModule("m", "m");
  VpiHandle sealed = AddStmt(module, "m.sealed", vpiWhile, true);

  ASSERT_NE(RegisterModuleWide(module), nullptr);
  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbStmt, sealed), 0);

  EXPECT_EQ(g_calls, 0);
  EXPECT_FALSE(Fired(sealed));
}

TEST_F(VpiModuleWideCallback, RegistrationOnOneStatementReachesNoSibling) {
  VpiHandle module = vpi_ctx_.CreateModule("m", "m");
  VpiHandle named = AddStmt(module, "m.a", vpiAssignment);
  VpiHandle sibling = AddStmt(module, "m.b", vpiWhile);

  ASSERT_NE(RegisterOnStatement(named), nullptr);
  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbStmt, sibling), 0);
  EXPECT_EQ(g_calls, 0);

  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbStmt, named), 1);
  EXPECT_EQ(g_calls, 1);
  EXPECT_TRUE(Fired(named));
}

int& ModuleWideRemovals() {
  static int removed = -1;
  return removed;
}

PLI_INT32 RemoveModuleWideCalltf(PLI_BYTE8*) {
  ModuleWideRemovals() = vpi_remove_cb(ModuleWideStmtCallback());
  return 0;
}

TEST_F(StmtCallbacksOfARun, TheOneHandleRemovesItFromEveryStatement) {
  ModuleWideRemovals() = -1;
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$unwatch");
  task.calltf = &RemoveModuleWideCalltf;
  ASSERT_NE(vpi_register_systf(&task), nullptr);
  RunWatchingTop(
      "module top; int a, b, c;\n"
      "  initial begin a = 1; #1 $unwatch; b = 2; #1 c = 3; end\n"
      "endmodule\n");
  EXPECT_EQ(ModuleWideRemovals(), 1);
  EXPECT_EQ(StmtTypesCalled(),
            (std::vector<int>{vpiBegin, vpiAssignment, vpiDelayControl,
                              vpiSysTaskCall}));
}

TEST(ModuleWideCallbackInASealedRun, AStatementInAnEnvelopeIsLeftOut) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  WatchStatementsOf("t");
  SimFixture f;
  RunUnderKey(SealedStatementsDesign(), kSealedStatementsKey, f);
  SetGlobalVpiContext(nullptr);
  EXPECT_NE(ModuleWideStmtCallback(), nullptr);
  EXPECT_EQ(StmtTypesCalled(),
            (std::vector<int>{vpiNamedBegin, vpiAssignment}));
}

}  // namespace
}  // namespace delta
