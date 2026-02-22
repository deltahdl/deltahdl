#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/net.h"
#include "simulation/sim_context.h"
#include "simulation/vpi.h"

namespace delta {
namespace {

class VpiClause3834Test : public ::testing::Test {
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

// §38.34: vpi_put_value

TEST_F(VpiClause3834Test, PutValueNoDelay) {
  auto *var = sim_ctx_.CreateVariable("d", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("d", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 77;
  vpiHandle ret = vpi_put_value(h, &val, nullptr, vpiNoDelay);
  EXPECT_NE(ret, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST_F(VpiClause3834Test, PutValueInertialDelay) {
  auto *var = sim_ctx_.CreateVariable("di", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("di", nullptr);
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 88;
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.low = 10;
  vpi_put_value(h, &val, &time, vpiInertialDelay);
  // For now, value is applied immediately regardless of delay mode.
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

TEST_F(VpiClause3834Test, PutValueTransportDelay) {
  auto *var = sim_ctx_.CreateVariable("dt", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("dt", nullptr);
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 99;
  s_vpi_time time = {};
  time.type = vpiSimTime;
  vpi_put_value(h, &val, &time, vpiTransportDelay);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST_F(VpiClause3834Test, PutValuePureTransportDelay) {
  auto *var = sim_ctx_.CreateVariable("dpt", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("dpt", nullptr);
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 55;
  vpi_put_value(h, &val, nullptr, vpiPureTransportDelay);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST_F(VpiClause3834Test, PutValueRealFormat) {
  auto *var = sim_ctx_.CreateVariable("rf", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("rf", nullptr);
  s_vpi_value val = {};
  val.format = vpiRealVal;
  val.value.real = 7.0;
  vpi_put_value(h, &val, nullptr, vpiNoDelay);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST_F(VpiClause3834Test, PutValueScalarFormat) {
  auto *var = sim_ctx_.CreateVariable("sf", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("sf", nullptr);
  s_vpi_value val = {};
  val.format = vpiScalarVal;
  val.value.scalar = vpi1;
  vpi_put_value(h, &val, nullptr, vpiNoDelay);
  EXPECT_EQ(var->value.words[0].aval & 1, 1u);
  EXPECT_EQ(var->value.words[0].bval & 1, 0u);
}

}  // namespace
}  // namespace delta
