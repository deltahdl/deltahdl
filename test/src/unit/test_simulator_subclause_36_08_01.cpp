#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

PLI_INT32 SizetfReturning12(PLI_BYTE8*) { return 12; }
PLI_INT32 SizetfReturning64(PLI_BYTE8*) { return 64; }

TEST(SizetfApplicationRoutine, ReturnValueIsTheFunctionReturnWidth) {
  s_vpi_systf_data sized = {};
  sized.type = kVpiSysFunc;
  sized.sysfunctype = kVpiSizedFunc;
  sized.sizetf = &SizetfReturning12;

  EXPECT_EQ(VpiSystfResultSizeBits(sized), 12);

  sized.sizetf = &SizetfReturning64;
  EXPECT_EQ(VpiSystfResultSizeBits(sized), 64);
}

TEST(SizetfApplicationRoutine, NoSizetfSpecifiedDefaultsTo32Bits) {
  s_vpi_systf_data sized = {};
  sized.type = kVpiSysFunc;
  sized.sysfunctype = kVpiSizedFunc;
  sized.sizetf = nullptr;

  EXPECT_EQ(VpiSystfResultSizeBits(sized), 32);
}

TEST(SizetfApplicationRoutine, NotCalledForSystemTask) {
  s_vpi_systf_data task = {};
  task.type = kVpiSysTask;
  task.sizetf = &SizetfReturning12;

  EXPECT_FALSE(VpiSystfSizetfIsCalled(task));
}

TEST(SizetfApplicationRoutine, NotCalledForRealValuedFunction) {
  s_vpi_systf_data real_func = {};
  real_func.type = kVpiSysFunc;
  real_func.sysfunctype = kVpiRealFunc;
  real_func.sizetf = &SizetfReturning12;

  EXPECT_FALSE(VpiSystfSizetfIsCalled(real_func));
}

int g_sizetf_runs = 0;

PLI_INT32 CountingSizetfReturning17(PLI_BYTE8*) {
  ++g_sizetf_runs;
  return 17;
}

PLI_INT32 PutsFortyTwoCalltf(PLI_BYTE8*) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 42;
  vpi_put_value(vpi_handle(vpiSysTfCall, nullptr), &value, nullptr, vpiNoDelay);
  return 0;
}

class SizetfInARun : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(SizetfInARun, ASizetfRunsOncePerRegistration) {
  g_sizetf_runs = 0;
  s_vpi_systf_data sized = {};
  sized.type = vpiSysFunc;
  sized.sysfunctype = vpiSizedFunc;
  sized.tfname = VpiText("$sized_once");
  sized.sizetf = &CountingSizetfReturning17;
  ASSERT_NE(vpi_register_systf(&sized), nullptr);

  const s_vpi_systf_data* registered = vpi_ctx_.ResolveSystf("$sized_once");
  ASSERT_NE(registered, nullptr);

  EXPECT_EQ(vpi_ctx_.SystfResultSizeBits(*registered), 17);
  EXPECT_EQ(vpi_ctx_.SystfResultSizeBits(*registered), 17);
  EXPECT_EQ(vpi_ctx_.SystfResultSizeBits(*registered), 17);
  EXPECT_EQ(g_sizetf_runs, 1);
}

TEST_F(SizetfInARun, ASizetfRunsBecauseTheFunctionAppearsInTheDesign) {
  g_sizetf_runs = 0;
  s_vpi_systf_data sized = {};
  sized.type = vpiSysFunc;
  sized.sysfunctype = vpiSizedFunc;
  sized.tfname = VpiText("$sized_once");
  sized.sizetf = &CountingSizetfReturning17;
  sized.calltf = &PutsFortyTwoCalltf;
  ASSERT_NE(vpi_register_systf(&sized), nullptr);
  EXPECT_EQ(g_sizetf_runs, 0);

  SimFixture f;
  RunAndFindVar(
      "module top;\n"
      "  int r;\n"
      "  initial r = $sized_once();\n"
      "endmodule\n",
      f, "r");

  EXPECT_EQ(g_sizetf_runs, 1);
}

TEST_F(SizetfInARun, TheCallsResultIsAsWideAsTheSizetfSaid) {
  g_sizetf_runs = 0;
  s_vpi_systf_data sized = {};
  sized.type = vpiSysFunc;
  sized.sysfunctype = vpiSizedFunc;
  sized.tfname = VpiText("$sized_once");
  sized.sizetf = &CountingSizetfReturning17;
  sized.calltf = &PutsFortyTwoCalltf;
  ASSERT_NE(vpi_register_systf(&sized), nullptr);

  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  int r;\n"
      "  initial r = $sized_once();\n"
      "endmodule\n",
      f, "r");

  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
  const s_vpi_systf_data* registered = vpi_ctx_.ResolveSystf("$sized_once");
  ASSERT_NE(registered, nullptr);
  EXPECT_EQ(vpi_ctx_.SystfResultSizeBits(*registered), 17);
  EXPECT_EQ(g_sizetf_runs, 1);
}

}  // namespace
}  // namespace delta
