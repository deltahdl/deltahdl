#include <gtest/gtest.h>

#include <cstdint>

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

PLI_UINT32 g_high_word = 0;
PLI_UINT32 g_low_word = 0;
int g_calltf_runs = 0;

PLI_INT32 PutsTheTwoWordsCalltf(PLI_BYTE8*) {
  ++g_calltf_runs;
  s_vpi_vecval words[2] = {};
  words[0].aval = static_cast<PLI_INT32>(g_low_word);
  words[1].aval = static_cast<PLI_INT32>(g_high_word);
  s_vpi_value value = {};
  value.format = vpiVectorVal;
  value.value.vector = words;
  vpi_put_value(vpi_handle(vpiSysTfCall, nullptr), &value, nullptr, vpiNoDelay);
  return 0;
}

PLI_INT32 PutsTwoAndAHalfCalltf(PLI_BYTE8*) {
  ++g_calltf_runs;
  s_vpi_value value = {};
  value.format = vpiRealVal;
  value.value.real = 2.5;
  vpi_put_value(vpi_handle(vpiSysTfCall, nullptr), &value, nullptr, vpiNoDelay);
  return 0;
}

void RegisterTheFunction(PLI_INT32 type, PLI_INT32 functype,
                         PLI_INT32 (*sizetf)(PLI_BYTE8*),
                         PLI_INT32 (*calltf)(PLI_BYTE8*)) {
  g_sizetf_runs = 0;
  g_calltf_runs = 0;
  s_vpi_systf_data data = {};
  data.type = type;
  data.sysfunctype = functype;
  data.tfname = VpiText("$w");
  data.sizetf = sizetf;
  data.calltf = calltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

void ExpectAnUnsizedCallGives(PLI_INT32 functype, PLI_UINT32 high_word,
                              PLI_UINT32 low_word, uint64_t wide) {
  g_high_word = high_word;
  g_low_word = low_word;
  RegisterTheFunction(vpiSysFunc, functype, nullptr, &PutsTheTwoWordsCalltf);
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  logic [63:0] r;\n"
      "  int b;\n"
      "  initial begin r = $w(); b = $bits($w()); end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), wide);
  auto* bits = f.ctx.FindVariable("b");
  ASSERT_NE(bits, nullptr);
  EXPECT_EQ(bits->value.ToUint64(), 32u);
  EXPECT_EQ(g_calltf_runs, 1);
}

TEST_F(SizetfInARun, ASizedFunctionWithNoSizetfReturns32Bits) {
  ExpectAnUnsizedCallGives(vpiSizedFunc, 0x5, 0xFFFFFFFF,
                           0x00000000FFFFFFFFull);
}

TEST_F(SizetfInARun, ASignedSizedFunctionWithNoSizetfReturns32SignedBits) {
  ExpectAnUnsizedCallGives(vpiSizedSignedFunc, 0x5, 0xFFFFFFFF,
                           0xFFFFFFFFFFFFFFFFull);
}

TEST_F(SizetfInARun, ASignedSizedFunctionWithBit31ClearIsNotExtended) {
  ExpectAnUnsizedCallGives(vpiSizedSignedFunc, 0x5, 0x7FFFFFFF,
                           0x000000007FFFFFFFull);
}

TEST_F(SizetfInARun, AFunctionWrittenOnlyInAnUncalledFunctionIsSized) {
  RegisterTheFunction(vpiSysFunc, vpiSizedFunc, &CountingSizetfReturning17,
                      &PutsFortyTwoCalltf);
  SimFixture f;
  RunAndFindVar(
      "module top;\n"
      "  int r;\n"
      "  function automatic int g(); return $w(); endfunction\n"
      "  initial r = 1;\n"
      "endmodule\n",
      f, "r");
  EXPECT_EQ(g_sizetf_runs, 1);
}

TEST_F(SizetfInARun, AFunctionWrittenOnlyAsABitsOperandIsSized) {
  RegisterTheFunction(vpiSysFunc, vpiSizedFunc, &CountingSizetfReturning17,
                      &PutsTheTwoWordsCalltf);
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  int r;\n"
      "  initial r = $bits($w());\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 17u);
  EXPECT_EQ(g_sizetf_runs, 1);
  EXPECT_EQ(g_calltf_runs, 0);
}

TEST_F(SizetfInARun, ASystemTasksSizetfIsNotCalled) {
  RegisterTheFunction(vpiSysTask, 0, &CountingSizetfReturning17,
                      &PutsTwoAndAHalfCalltf);
  SimFixture f;
  RunAndFindVar(
      "module top;\n"
      "  int r;\n"
      "  initial begin $w; r = 1; end\n"
      "endmodule\n",
      f, "r");
  EXPECT_EQ(g_calltf_runs, 1);
  EXPECT_EQ(g_sizetf_runs, 0);
}

TEST_F(SizetfInARun, ARealFunctionsSizetfIsNotCalled) {
  RegisterTheFunction(vpiSysFunc, vpiRealFunc, &CountingSizetfReturning17,
                      &PutsTwoAndAHalfCalltf);
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  int r;\n"
      "  initial r = $rtoi($w() * 2.0);\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
  EXPECT_EQ(g_calltf_runs, 1);
  EXPECT_EQ(g_sizetf_runs, 0);
}

}  // namespace
}  // namespace delta
