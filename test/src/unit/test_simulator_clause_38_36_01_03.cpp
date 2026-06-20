#include <gtest/gtest.h>

#include <algorithm>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §38.36.1.3 ("Registering callbacks on module-wide basis") states three
// things. (1) Passing a handle to a module instance in the obj field of the
// s_cb_data structure places a cbStmt callback on every statement in the module
// that can have one. (2) The call returns a single callback object that can be
// passed to vpi_remove_cb() to remove the callback on every statement in the
// module instance at once. (3) Statements that reside in protected portions of
// the code shall not have callbacks placed on them. These tests build a module
// instance, register a cbStmt callback against it, and observe
// vpi_register_cb()/ DispatchCallbacks()/RemoveCb() applying those rules.

// Records the obj field of each s_cb_data the simulator hands to the routine,
// so a test can confirm which statements the module-wide callback fired on.
int g_calls = 0;
std::vector<vpiHandle> g_objs;

int RecordCb(VpiCbData* data) {
  ++g_calls;
  if (data) g_objs.push_back(data->obj);
  return 0;
}

bool Fired(vpiHandle stmt) {
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

  // Build a statement object of the given VPI type, parented under `module` as
  // one of its children. `protect` marks the statement as residing in a
  // protected portion of the code.
  vpiHandle AddStmt(vpiHandle module, const char* name, int type,
                    bool protect = false) {
    vpiHandle h = vpi_ctx_.CreateModule(name, name);
    h->type = type;
    h->is_protected = protect;
    module->children.push_back(h);
    return h;
  }

  // Register a cbStmt callback whose obj is the given module instance.
  vpiHandle RegisterModuleWide(vpiHandle module) {
    s_cb_data cb = {};
    cb.reason = cbStmt;
    cb.obj = module;
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

// §38.36.1.3: a handle to a module instance in obj places a callback on every
// statement in the module that can have one. Registering once against the
// module and dispatching cbStmt fires the routine on each statement - including
// one nested inside a block - and never on the module itself.
TEST_F(VpiModuleWideCallback, PlacesCallbackOnEveryStatementIncludingNested) {
  vpiHandle module = vpi_ctx_.CreateModule("m", "m");
  vpiHandle flat = AddStmt(module, "m.a", vpiAssignment);
  vpiHandle block = AddStmt(module, "m.blk", vpiNamedBegin);
  vpiHandle nested = AddStmt(block, "m.blk.s", vpiWhile);

  ASSERT_NE(RegisterModuleWide(module), nullptr);
  vpi_ctx_.DispatchCallbacks(cbStmt);

  EXPECT_EQ(g_calls, 3);
  EXPECT_TRUE(Fired(flat));
  EXPECT_TRUE(Fired(block));
  EXPECT_TRUE(Fired(nested));
  EXPECT_FALSE(Fired(module));
}

// §38.36.1.3: only statements receive the callback. A child of the module that
// is not a statement-class object (here a net) is left out of the module-wide
// fan-out.
TEST_F(VpiModuleWideCallback, NonStatementChildrenGetNoCallback) {
  vpiHandle module = vpi_ctx_.CreateModule("m", "m");
  vpiHandle stmt = AddStmt(module, "m.s", vpiAssignment);
  vpiHandle net = AddStmt(module, "m.n", vpiNet);

  ASSERT_NE(RegisterModuleWide(module), nullptr);
  vpi_ctx_.DispatchCallbacks(cbStmt);

  EXPECT_EQ(g_calls, 1);
  EXPECT_TRUE(Fired(stmt));
  EXPECT_FALSE(Fired(net));
}

// §38.36.1.3: statements that reside in protected portions of the code shall
// not have callbacks placed on them. A protected statement in the module is
// skipped, while an unprotected sibling still fires.
TEST_F(VpiModuleWideCallback, ProtectedStatementsGetNoCallback) {
  vpiHandle module = vpi_ctx_.CreateModule("m", "m");
  vpiHandle open = AddStmt(module, "m.open", vpiAssignment, /*protect=*/false);
  vpiHandle sealed = AddStmt(module, "m.sealed", vpiWhile, /*protect=*/true);

  ASSERT_NE(RegisterModuleWide(module), nullptr);
  vpi_ctx_.DispatchCallbacks(cbStmt);

  EXPECT_EQ(g_calls, 1);
  EXPECT_TRUE(Fired(open));
  EXPECT_FALSE(Fired(sealed));
}

// §38.36.1.3: module-wide registration applies to the module instance. The walk
// does not cross into a nested module instance, which owns its own statements;
// a statement inside the sub-instance does not fire.
TEST_F(VpiModuleWideCallback, NestedModuleInstanceIsNotReached) {
  vpiHandle module = vpi_ctx_.CreateModule("m", "m");
  vpiHandle own = AddStmt(module, "m.s", vpiAssignment);
  vpiHandle sub = vpi_ctx_.CreateModule("m.sub", "m.sub");
  module->children.push_back(sub);
  vpiHandle subStmt = AddStmt(sub, "m.sub.s", vpiAssignment);

  ASSERT_NE(RegisterModuleWide(module), nullptr);
  vpi_ctx_.DispatchCallbacks(cbStmt);

  EXPECT_EQ(g_calls, 1);
  EXPECT_TRUE(Fired(own));
  EXPECT_FALSE(Fired(subStmt));
}

// §38.36.1.3: "every statement that can have a callback" is the empty set when
// a module instance holds no eligible statements. Registration still yields a
// single callback object, but dispatching cbStmt fires nothing - the
// module-wide record is consumed by the fan-out and never delivers a callback
// on the module itself.
TEST_F(VpiModuleWideCallback, ModuleWithNoStatementsFiresNothing) {
  vpiHandle module = vpi_ctx_.CreateModule("m", "m");

  ASSERT_NE(RegisterModuleWide(module), nullptr);
  vpi_ctx_.DispatchCallbacks(cbStmt);

  EXPECT_EQ(g_calls, 0);
  EXPECT_FALSE(Fired(module));
}

// §38.36.1.3: registering against a module returns a single callback object;
// removing that one handle with vpi_remove_cb() removes the callback on every
// statement in the module instance. After removal, dispatching cbStmt fires
// nothing.
TEST_F(VpiModuleWideCallback, SingleHandleRemovesCallbackFromEveryStatement) {
  vpiHandle module = vpi_ctx_.CreateModule("m", "m");
  AddStmt(module, "m.a", vpiAssignment);
  AddStmt(module, "m.b", vpiWhile);

  vpiHandle cb = RegisterModuleWide(module);
  ASSERT_NE(cb, nullptr);

  vpi_ctx_.DispatchCallbacks(cbStmt);
  EXPECT_EQ(g_calls, 2);

  EXPECT_EQ(vpi_ctx_.RemoveCb(cb), 1);
  g_calls = 0;
  g_objs.clear();
  vpi_ctx_.DispatchCallbacks(cbStmt);
  EXPECT_EQ(g_calls, 0);
}

}  // namespace
}  // namespace delta
