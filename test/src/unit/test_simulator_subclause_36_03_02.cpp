#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "parser/ast_specify.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class OverrideBuiltinSystf : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(OverrideBuiltinSystf, UnclaimedBuiltinNameResolvesToNothing) {
  EXPECT_EQ(vpi_ctx_.ResolveSystf("$random"), nullptr);
}

TEST_F(OverrideBuiltinSystf, UserApplicationOverridesBuiltinName) {
  static int called = 0;
  called = 0;
  auto user_random = [](PLI_BYTE8*) -> PLI_INT32 {
    called = 1;
    return 0;
  };

  s_vpi_systf_data data = {};
  data.type = vpiSysFunc;
  data.sysfunctype = vpiIntFunc;
  data.tfname = VpiText("$random");
  data.calltf = user_random;

  ASSERT_NE(vpi_register_systf(&data), nullptr);

  const s_vpi_systf_data* resolved = vpi_ctx_.ResolveSystf("$random");
  ASSERT_NE(resolved, nullptr);
  EXPECT_STREQ(resolved->tfname, "$random");
  ASSERT_NE(resolved->calltf, nullptr);

  resolved->calltf(nullptr);
  EXPECT_EQ(called, 1);
}

TEST_F(OverrideBuiltinSystf, LaterRegistrationOverridesEarlierOfSameName) {
  auto builtin_impl = [](PLI_BYTE8*) -> PLI_INT32 { return 1; };
  auto user_impl = [](PLI_BYTE8*) -> PLI_INT32 { return 2; };

  s_vpi_systf_data builtin = {};
  builtin.type = vpiSysFunc;
  builtin.sysfunctype = vpiIntFunc;
  builtin.tfname = VpiText("$random");
  builtin.calltf = builtin_impl;

  s_vpi_systf_data user = {};
  user.type = vpiSysFunc;
  user.sysfunctype = vpiIntFunc;
  user.tfname = VpiText("$random");
  user.calltf = user_impl;

  ASSERT_NE(vpi_register_systf(&builtin), nullptr);
  ASSERT_NE(vpi_register_systf(&user), nullptr);

  const s_vpi_systf_data* resolved = vpi_ctx_.ResolveSystf("$random");
  ASSERT_NE(resolved, nullptr);
  ASSERT_NE(resolved->calltf, nullptr);
  EXPECT_EQ(resolved->calltf(nullptr), 2);
}

TEST_F(OverrideBuiltinSystf, SignedAndUnsignedCanBeOverridden) {
  s_vpi_systf_data signed_fn = {};
  signed_fn.type = vpiSysFunc;
  signed_fn.sysfunctype = vpiSizedSignedFunc;
  signed_fn.tfname = VpiText("$signed");

  s_vpi_systf_data unsigned_fn = {};
  unsigned_fn.type = vpiSysFunc;
  unsigned_fn.sysfunctype = vpiSizedFunc;
  unsigned_fn.tfname = VpiText("$unsigned");

  ASSERT_NE(vpi_register_systf(&signed_fn), nullptr);
  ASSERT_NE(vpi_register_systf(&unsigned_fn), nullptr);

  const s_vpi_systf_data* rs = vpi_ctx_.ResolveSystf("$signed");
  const s_vpi_systf_data* ru = vpi_ctx_.ResolveSystf("$unsigned");
  ASSERT_NE(rs, nullptr);
  ASSERT_NE(ru, nullptr);
  EXPECT_STREQ(rs->tfname, "$signed");
  EXPECT_STREQ(ru->tfname, "$unsigned");
}

TEST_F(OverrideBuiltinSystf, OverriddenSignedHasSameWidthForAllInstances) {
  auto fixed_width = [](PLI_BYTE8*) -> PLI_INT32 { return 17; };

  s_vpi_systf_data signed_fn = {};
  signed_fn.type = vpiSysFunc;
  signed_fn.sysfunctype = vpiSizedSignedFunc;
  signed_fn.tfname = VpiText("$signed");
  signed_fn.sizetf = fixed_width;

  ASSERT_NE(vpi_register_systf(&signed_fn), nullptr);

  const s_vpi_systf_data* resolved = vpi_ctx_.ResolveSystf("$signed");
  ASSERT_NE(resolved, nullptr);

  int first = VpiSystfResultSizeBits(*resolved);
  int second = VpiSystfResultSizeBits(*resolved);
  EXPECT_EQ(first, 17);
  EXPECT_EQ(second, 17);
  EXPECT_EQ(first, second);
}

TEST_F(OverrideBuiltinSystf, NullNameResolvesToNothing) {
  EXPECT_EQ(vpi_ctx_.ResolveSystf(nullptr), nullptr);
}

TEST_F(OverrideBuiltinSystf, UserTaskApplicationOverridesBuiltinName) {
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$monitor");

  ASSERT_NE(vpi_register_systf(&task), nullptr);

  const s_vpi_systf_data* resolved = vpi_ctx_.ResolveSystf("$monitor");
  ASSERT_NE(resolved, nullptr);
  EXPECT_STREQ(resolved->tfname, "$monitor");
  EXPECT_EQ(resolved->type, vpiSysTask);
}

TEST_F(OverrideBuiltinSystf,
       NonMatchingRegistrationsLeaveBuiltinNameUnclaimed) {
  s_vpi_systf_data other = {};
  other.type = vpiSysFunc;
  other.sysfunctype = vpiIntFunc;
  other.tfname = VpiText("$my_func");

  ASSERT_NE(vpi_register_systf(&other), nullptr);

  EXPECT_EQ(vpi_ctx_.ResolveSystf("$random"), nullptr);
}

int g_setup_calls = 0;

PLI_INT32 SetupCalltf(PLI_BYTE8*) {
  ++g_setup_calls;
  return 0;
}

TEST_F(OverrideBuiltinSystf, ATimingCheckCannotBeOverridden) {
  g_setup_calls = 0;
  s_vpi_systf_data setup = {};
  setup.type = vpiSysTask;
  setup.tfname = VpiText("$setup");
  setup.calltf = SetupCalltf;
  ASSERT_NE(vpi_register_systf(&setup), nullptr);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 7);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  EXPECT_EQ(g_setup_calls, 0);
  const SpecifyManager* mgr = f.ctx.GetSpecifyManager();
  ASSERT_NE(mgr, nullptr);
  bool registered_as_a_check = false;
  for (const auto& check : mgr->GetTimingChecks()) {
    if (check.kind == TimingCheckKind::kSetup) registered_as_a_check = true;
  }
  EXPECT_TRUE(registered_as_a_check);
}

}  // namespace
}  // namespace delta
