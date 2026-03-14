#include <gtest/gtest.h>

#include <cstring>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiGetValueSim : public ::testing::Test {
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

TEST_F(VpiGetValueSim, GetValueIntFormat) {
  auto* var = sim_ctx_.CreateVariable("x", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 123);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("x", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiIntVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.integer, 123);
}

TEST_F(VpiGetValueSim, GetValueRealFormat) {
  auto* var = sim_ctx_.CreateVariable("r", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 42);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("r", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiRealVal;
  vpi_get_value(h, &val);
  EXPECT_DOUBLE_EQ(val.value.real, 42.0);
}

TEST_F(VpiGetValueSim, GetValueScalarFormatZero) {
  auto* var = sim_ctx_.CreateVariable("s", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("s", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.scalar, vpi0);
}

TEST_F(VpiGetValueSim, GetValueScalarFormatOne) {
  auto* var = sim_ctx_.CreateVariable("s1", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 1);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("s1", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.scalar, vpi1);
}

TEST_F(VpiGetValueSim, GetValueBinStrFormat) {
  auto* var = sim_ctx_.CreateVariable("b", 4);
  var->value = MakeLogic4VecVal(arena_, 4, 0b1010);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("b", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiBinStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "1010");
}

TEST_F(VpiGetValueSim, GetValueHexStrFormat) {
  auto* var = sim_ctx_.CreateVariable("hx", 8);
  var->value = MakeLogic4VecVal(arena_, 8, 0xAB);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("hx", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiHexStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "ab");
}

TEST_F(VpiGetValueSim, GetValueOctStrFormat) {
  auto* var = sim_ctx_.CreateVariable("oc", 6);
  var->value = MakeLogic4VecVal(arena_, 6, 075);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("oc", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiOctStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "75");
}

TEST_F(VpiGetValueSim, GetValueStringFormat) {
  auto* var = sim_ctx_.CreateVariable("sv", 32);

  var->value = MakeLogic4VecVal(arena_, 32, 0x00004142);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("sv", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiStringVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "AB");
}

TEST_F(VpiGetValueSim, GetValueTimeFormat) {
  auto* var = sim_ctx_.CreateVariable("t", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 500);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("t", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiTimeVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.integer, 500);
}

}  // namespace
}  // namespace delta
