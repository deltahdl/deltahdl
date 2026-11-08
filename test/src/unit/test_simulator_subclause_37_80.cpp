#include <gtest/gtest.h>

#include <array>
#include <cstddef>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class Callback : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(Callback, NullReferenceIterationReachesRegisteredCallback) {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  vpiHandle registered = vpi_register_cb(&cb);
  ASSERT_NE(registered, nullptr);

  vpiHandle it = vpi_iterate(vpiCallback, nullptr);
  ASSERT_NE(it, nullptr);

  vpiHandle reached = vpi_scan(it);
  ASSERT_NE(reached, nullptr);
  EXPECT_EQ(VpiObjectOf(reached)->type, vpiCallback);
  EXPECT_EQ(reached, registered);

  EXPECT_EQ(vpi_scan(it), nullptr);
}

TEST_F(Callback, CallbackInfoIsReadableFromIteratedCallback) {
  s_cb_data cb = {};
  cb.reason = cbStartOfSimulation;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  vpiHandle it = vpi_iterate(vpiCallback, nullptr);
  ASSERT_NE(it, nullptr);
  vpiHandle reached = vpi_scan(it);
  ASSERT_NE(reached, nullptr);

  s_cb_data info = {};
  vpi_get_cb_info(reached, &info);
  EXPECT_EQ(info.reason, cbStartOfSimulation);
}

namespace {
void ExpectCallbackReachedFromObject(int object_type) {
  VpiObject object;
  object.type = object_type;

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = VpiHandleOf(&object);
  vpiHandle registered = vpi_register_cb(&cb);
  ASSERT_NE(registered, nullptr);

  EXPECT_EQ(vpi_handle(vpiCallback, VpiHandleOf(&object)), registered);

  vpiHandle it = vpi_iterate(vpiCallback, VpiHandleOf(&object));
  ASSERT_NE(it, nullptr);
  vpiHandle reached = vpi_scan(it);
  ASSERT_NE(reached, nullptr);
  EXPECT_EQ(VpiObjectOf(reached)->type, vpiCallback);
  EXPECT_EQ(reached, registered);
  EXPECT_EQ(vpi_scan(it), nullptr);

  EXPECT_EQ(vpi_iterate(vpiCallback, nullptr), nullptr);
}
}  // namespace

TEST_F(Callback, CallbackOnPrimTermIsReachedFromPrimTerm) {
  ExpectCallbackReachedFromObject(vpiPrimTerm);
}

TEST_F(Callback, CallbackOnExprIsReachedFromExpr) {
  ExpectCallbackReachedFromObject(vpiOperation);
}

TEST_F(Callback, CallbackOnTimeQueueIsReachedFromTimeQueue) {
  ExpectCallbackReachedFromObject(vpiTimeQueue);
}

TEST_F(Callback, CallbackIterationFromObjectIsScopedToThatObject) {
  VpiObject target;
  target.type = vpiAssignStmt;
  VpiObject other;
  other.type = vpiAssignStmt;

  s_cb_data on_target = {};
  on_target.reason = cbValueChange;
  on_target.obj = VpiHandleOf(&target);
  vpiHandle target_cb = vpi_register_cb(&on_target);
  ASSERT_NE(target_cb, nullptr);

  s_cb_data on_other = {};
  on_other.reason = cbValueChange;
  on_other.obj = VpiHandleOf(&other);
  ASSERT_NE(vpi_register_cb(&on_other), nullptr);

  s_cb_data unrelated = {};
  unrelated.reason = cbEndOfSimulation;
  ASSERT_NE(vpi_register_cb(&unrelated), nullptr);

  vpiHandle it = vpi_iterate(vpiCallback, VpiHandleOf(&target));
  ASSERT_NE(it, nullptr);
  vpiHandle reached = vpi_scan(it);
  ASSERT_NE(reached, nullptr);
  EXPECT_EQ(reached, target_cb);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

TEST_F(Callback, IterationFromObjectWithoutCallbackYieldsNoIterator) {
  VpiObject with_callback;
  with_callback.type = vpiAssignStmt;
  VpiObject without_callback;
  without_callback.type = vpiAssignStmt;

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = VpiHandleOf(&with_callback);
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  EXPECT_EQ(vpi_iterate(vpiCallback, VpiHandleOf(&without_callback)), nullptr);
}

TEST_F(Callback, TheSingleArrowIsDrawnFromEveryKindTheTwoClassesGroup) {
  constexpr std::array<int, 8> kHostKinds = {
      vpiPrimTerm, vpiTimeQueue, vpiOperation,  vpiConstant,
      vpiRefObj,   vpiBegin,     vpiAssignment, vpiForever};
  std::array<VpiObject, kHostKinds.size()> objects;
  std::array<vpiHandle, kHostKinds.size()> registered = {};

  for (size_t i = 0; i < kHostKinds.size(); ++i) {
    objects[i].type = kHostKinds[i];

    s_cb_data cb = {};
    cb.reason = cbValueChange;
    cb.obj = VpiHandleOf(&objects[i]);
    registered[i] = vpi_register_cb(&cb);
    ASSERT_NE(registered[i], nullptr) << "host kind " << kHostKinds[i];
  }

  for (size_t i = 0; i < kHostKinds.size(); ++i) {
    EXPECT_EQ(vpi_handle(vpiCallback, VpiHandleOf(&objects[i])), registered[i])
        << "host kind " << kHostKinds[i];
  }
}

TEST_F(Callback, TheSingleArrowReachesNothingWhereTheDiagramDrawsNone) {
  VpiObject without_callback;
  without_callback.type = vpiAssignStmt;
  EXPECT_EQ(vpi_handle(vpiCallback, VpiHandleOf(&without_callback)), nullptr);

  VpiObject module;
  module.type = vpiModule;

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = VpiHandleOf(&module);
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  EXPECT_EQ(vpi_handle(vpiCallback, VpiHandleOf(&module)), nullptr);
}

TEST_F(Callback, NullReferenceIterationReachesOnlyTheUnrelatedCallbacks) {
  VpiObject statement;
  statement.type = vpiAssignStmt;
  VpiObject module;
  module.type = vpiModule;

  s_cb_data on_stmt = {};
  on_stmt.reason = cbValueChange;
  on_stmt.obj = VpiHandleOf(&statement);
  vpiHandle stmt_cb = vpi_register_cb(&on_stmt);
  ASSERT_NE(stmt_cb, nullptr);

  s_cb_data on_module = {};
  on_module.reason = cbValueChange;
  on_module.obj = VpiHandleOf(&module);
  vpiHandle module_cb = vpi_register_cb(&on_module);
  ASSERT_NE(module_cb, nullptr);

  s_cb_data on_nothing = {};
  on_nothing.reason = cbEndOfSimulation;
  vpiHandle free_cb = vpi_register_cb(&on_nothing);
  ASSERT_NE(free_cb, nullptr);

  vpiHandle it = vpi_iterate(vpiCallback, nullptr);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(vpi_scan(it), module_cb);
  EXPECT_EQ(vpi_scan(it), free_cb);
  EXPECT_EQ(vpi_scan(it), nullptr);

  EXPECT_EQ(vpi_handle(vpiCallback, VpiHandleOf(&statement)), stmt_cb);
}

TEST_F(Callback, TheSingleArrowReachesNothingOnceTheCallbackIsRemoved) {
  VpiObject statement;
  statement.type = vpiAssignStmt;

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = VpiHandleOf(&statement);
  vpiHandle registered = vpi_register_cb(&cb);
  ASSERT_NE(registered, nullptr);
  ASSERT_EQ(vpi_handle(vpiCallback, VpiHandleOf(&statement)), registered);

  EXPECT_EQ(vpi_remove_cb(registered), 1);
  EXPECT_EQ(vpi_handle(vpiCallback, VpiHandleOf(&statement)), nullptr);
}

TEST_F(Callback, ANetAndAVariableReachTheirCallbacks) {
  VpiObject net;
  net.type = vpiNet;
  VpiObject var;
  var.type = vpiReg;

  s_cb_data on_net = {};
  on_net.reason = cbForce;
  on_net.obj = VpiHandleOf(&net);
  vpiHandle net_cb = vpi_register_cb(&on_net);
  ASSERT_NE(net_cb, nullptr);

  s_cb_data on_var = {};
  on_var.reason = cbForce;
  on_var.obj = VpiHandleOf(&var);
  vpiHandle var_cb = vpi_register_cb(&on_var);
  ASSERT_NE(var_cb, nullptr);

  EXPECT_EQ(vpi_handle(vpiCallback, VpiHandleOf(&net)), net_cb);
  EXPECT_EQ(vpi_handle(vpiCallback, VpiHandleOf(&var)), var_cb);
  EXPECT_EQ(vpi_iterate(vpiCallback, nullptr), nullptr);
}

}  // namespace
}  // namespace delta
