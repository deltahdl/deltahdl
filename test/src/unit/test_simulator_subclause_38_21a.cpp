#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_vpi_run.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiHandleByNameSim : public ::testing::Test {
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

TEST_F(VpiHandleByNameSim, HandleByNameFindsModule) {
  vpi_ctx_.CreateModule("dut", "dut");
  vpiHandle h = vpi_handle_by_name(VpiText("dut"), nullptr);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(vpi_get(vpiType, h), vpiModule);
}

TEST_F(VpiHandleByNameSim, HandleByNameNullReturnsNullptr) {
  vpiHandle h = vpi_handle_by_name(nullptr, nullptr);
  EXPECT_EQ(h, nullptr);
}

TEST_F(VpiHandleByNameSim, ScopeConfinesSearch) {
  vpi_ctx_.CreateModule("alpha", "alpha");
  VpiHandle top = vpi_ctx_.CreateModule("top", "top");
  VpiHandle beta = vpi_ctx_.CreatePort("beta", kVpiInput, top);

  EXPECT_EQ(VpiObjectOf(vpi_handle_by_name(VpiText("beta"), VpiHandleOf(top))),
            beta);
  EXPECT_EQ(vpi_handle_by_name(VpiText("alpha"), VpiHandleOf(top)), nullptr);
}

TEST_F(VpiHandleByNameSim, HierarchicalNameResolves) {
  VpiHandle top = vpi_ctx_.CreateModule("top", "top");
  VpiHandle beta = vpi_ctx_.CreatePort("beta", kVpiInput, top);

  EXPECT_EQ(VpiObjectOf(vpi_handle_by_name(VpiText("top.beta"), nullptr)),
            beta);
}

TEST_F(VpiHandleByNameSim, ProtectedScopeIsError) {
  VpiHandle locked = vpi_ctx_.CreateModule("sec", "sec");
  locked->is_protected = true;
  vpi_ctx_.CreatePort("inner", kVpiInput, locked);

  EXPECT_EQ(vpi_handle_by_name(VpiText("inner"), VpiHandleOf(locked)), nullptr);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

TEST_F(VpiHandleByNameSim, HierarchicalThroughProtectedScopeIsError) {
  VpiHandle root = vpi_ctx_.CreateModule("root", "root");
  VpiHandle mid = vpi_ctx_.CreatePort("mid", kVpiInput, root);
  mid->is_protected = true;
  vpi_ctx_.CreatePort("deep", kVpiInput, mid);

  EXPECT_EQ(vpi_handle_by_name(VpiText("root.mid.deep"), nullptr), nullptr);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

TEST_F(VpiHandleByNameSim, NameMatchingNoObjectReturnsNull) {
  vpi_ctx_.CreateModule("present", "present");

  EXPECT_EQ(vpi_handle_by_name(VpiText("absent"), nullptr), nullptr);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
}

TEST_F(VpiHandleByNameSim, HandleByNameFindsRuntimeVariable) {
  sim_ctx_.CreateVariable("counter", 8);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("counter"), nullptr);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(vpi_get(vpiType, h), vpiReg);
}

class NamesOfARun : public VpiDesignRun {};

TEST_F(NamesOfARun, APackageMemberIsFoundByItsFullName) {
  Run("package pkg; parameter int P = 42; int pv = 8; endpackage\n"
      "module top; endmodule\n");
  vpiHandle parameter = By("pkg::P");
  ASSERT_NE(parameter, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, parameter), "pkg::P");
  vpiHandle variable = By("pkg::pv");
  ASSERT_NE(variable, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, variable), "pkg::pv");
}

TEST_F(NamesOfARun, ACompilationUnitItemIsNotFoundThroughItsScope) {
  Run("int g = 3;\n"
      "module top; int x = $unit::g; endmodule\n");
  EXPECT_EQ(By("$unit::g"), nullptr);
}

TEST_F(NamesOfARun, AnEscapedComponentIsFoundByItsIdentifier) {
  Run("module top; int \\my-var = 3; endmodule\n");
  vpiHandle var = By("top.\\my-var ");
  ASSERT_NE(var, nullptr);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(var, &value);
  EXPECT_EQ(value.value.integer, 3);
}

}  // namespace
}  // namespace delta
