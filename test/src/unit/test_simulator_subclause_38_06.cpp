#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
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

class VpiGetPropertySim : public ::testing::Test {
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

TEST_F(VpiGetPropertySim, GetTypeForModule) {
  auto* mod = vpi_ctx_.CreateModule("m", "m");
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(mod)), vpiModule);
}

TEST_F(VpiGetPropertySim, GetDirectionForPort) {
  auto* mod = vpi_ctx_.CreateModule("m", "m");
  auto* port = vpi_ctx_.CreatePort("din", kVpiInput, mod);
  EXPECT_EQ(vpi_get(vpiDirection, VpiHandleOf(port)), vpiInput);
}

TEST_F(VpiGetPropertySim, GetSizeForVariable) {
  auto* var = sim_ctx_.CreateVariable("wide", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("wide"), nullptr);
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(vpi_get(vpiSize, h), 32);
}

TEST_F(VpiGetPropertySim, NullHandleIsAnErrorForAnObjectProperty) {
  EXPECT_EQ(vpi_get(vpiSize, nullptr), vpiUndefined);
  EXPECT_NE(vpi_chk_error(nullptr), 0);
  EXPECT_EQ(vpi_get64(vpiSize, nullptr), vpiUndefined);
  EXPECT_NE(vpi_chk_error(nullptr), 0);
  EXPECT_EQ(vpi_get(vpiType, nullptr), vpiUndefined);
}

TEST_F(VpiGetPropertySim, NullHandleStillAnswersTheRunsProperties) {
  EXPECT_EQ(vpi_get(vpiTimeUnit, nullptr),
            vpi_ctx_.SmallestModuleTimePrecision());
  EXPECT_EQ(vpi_chk_error(nullptr), 0);
  EXPECT_NE(vpi_get(vpiSaveRestartID, nullptr), vpiUndefined);
  EXPECT_EQ(vpi_chk_error(nullptr), 0);
}

TEST_F(VpiGetPropertySim, BooleanPropertyReportsOneForTrue) {
  sim_ctx_.CreateVariable("loc", 8);
  vpi_ctx_.Attach(sim_ctx_);
  vpiHandle h = vpi_handle_by_name(VpiText("loc"), nullptr);
  ASSERT_NE(h, nullptr);
  VpiObjectOf(h)->automatic = true;
  EXPECT_EQ(vpi_get(vpiAutomatic, h), 1);
}

TEST_F(VpiGetPropertySim, BooleanPropertyReportsZeroForFalse) {
  sim_ctx_.CreateVariable("stat", 8);
  vpi_ctx_.Attach(sim_ctx_);
  vpiHandle h = vpi_handle_by_name(VpiText("stat"), nullptr);
  ASSERT_NE(h, nullptr);
  VpiObjectOf(h)->automatic = false;
  EXPECT_EQ(vpi_get(vpiAutomatic, h), 0);
}

TEST_F(VpiGetPropertySim, TimePropertyWithNullObjectReportsSimulationTimeUnit) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  mod->time_precision = -9;
  EXPECT_EQ(vpi_get(vpiTimeUnit, nullptr), -9);
  EXPECT_EQ(vpi_get(vpiTimePrecision, nullptr), -9);
}

TEST_F(VpiGetPropertySim, ProtectedObjectQueryReturnsVpiUndefined) {
  auto* mod = vpi_ctx_.CreateModule("locked", "locked");
  mod->is_protected = true;

  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(mod)), vpiModule);

  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(mod)), vpiUndefined);

  s_vpi_error_info info = {};
  EXPECT_NE(vpi_chk_error(&info), 0);
  EXPECT_NE(info.level, 0);
}

TEST_F(VpiGetPropertySim, ProtectedObjectStillReportsIsProtectedAsBooleanTrue) {
  auto* mod = vpi_ctx_.CreateModule("sealed", "sealed");
  mod->is_protected = true;

  EXPECT_EQ(vpi_get(vpiIsProtected, VpiHandleOf(mod)), 1);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

}  // namespace
}  // namespace delta
