#include <gtest/gtest.h>

#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class Iterator : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(Iterator, IteratorTypeReportsTheWalkedKind) {
  VpiObject child_module;
  child_module.type = vpiModule;
  VpiObject child_port;
  child_port.type = vpiPort;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&child_module, &child_port};

  vpiHandle module_iter = vpi_iterate(vpiModule, VpiHandleOf(&scope));
  ASSERT_NE(module_iter, nullptr);
  EXPECT_EQ(vpi_get(vpiIteratorType, module_iter), vpiModule);

  vpiHandle port_iter = vpi_iterate(vpiPort, VpiHandleOf(&scope));
  ASSERT_NE(port_iter, nullptr);
  EXPECT_EQ(vpi_get(vpiIteratorType, port_iter), vpiPort);
}

TEST_F(Iterator, UseRecoversTheReferenceHandle) {
  VpiObject child_module;
  child_module.type = vpiModule;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&child_module};

  vpiHandle iter = vpi_iterate(vpiModule, VpiHandleOf(&scope));
  ASSERT_NE(iter, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiUse, iter)), &scope);
}

TEST_F(Iterator, UseReturnsNullForAnIteratorCreatedOverANullReference) {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  vpiHandle iter = vpi_iterate(vpiCallback, nullptr);
  ASSERT_NE(iter, nullptr);

  EXPECT_EQ(vpi_handle(vpiUse, iter), nullptr);
  EXPECT_EQ(vpi_get(vpiIteratorType, iter), vpiCallback);
}

TEST_F(Iterator, TheTypeAndTheEdgeAreDrawnOnTheIteratorAlone) {
  VpiObject scope;
  scope.type = vpiModule;

  EXPECT_EQ(vpi_get(vpiIteratorType, VpiHandleOf(&scope)), vpiUndefined);
  EXPECT_EQ(vpi_handle(vpiUse, VpiHandleOf(&scope)), nullptr);
}

}  // namespace
}  // namespace delta
