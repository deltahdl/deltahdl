#include <gtest/gtest.h>

#include <cstdint>
#include <string>

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

PLI_INT32 PutFixedPattern(PLI_BYTE8*) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 0x1ABCD;
  vpi_put_value(vpi_handle(vpiSysTfCall, nullptr), &value, nullptr, vpiNoDelay);
  return 0;
}

PLI_INT32 SizeSeventeen(PLI_BYTE8*) { return 17; }

void RegisterSizedOverride(const char* name, PLI_INT32 (*sizetf)(PLI_BYTE8*)) {
  s_vpi_systf_data func = {};
  func.type = vpiSysFunc;
  func.sysfunctype = vpiSizedFunc;
  func.tfname = VpiText(name);
  func.calltf = PutFixedPattern;
  func.sizetf = sizetf;
  ASSERT_NE(vpi_register_systf(&func), nullptr);
}

uint64_t ValueAfterRun(SimFixture& f, const char* name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? ~uint64_t{0} : var->value.ToUint64();
}

void RunOverridden(const std::string& body, SimFixture& f) {
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a4 = 4'h1;\n"
      "  logic [7:0] a8 = 8'h1;\n"
      "  logic [39:0] a40 = 40'h1;\n" +
          body + "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST_F(OverrideBuiltinSystf, ADesignCallOfAnOverriddenRandomGetsTheAppsValue) {
  RegisterSizedOverride("$random", nullptr);
  SimFixture f;
  RunOverridden(
      "  int r;\n"
      "  initial r = $random;\n",
      f);
  EXPECT_EQ(ValueAfterRun(f, "r"), 0x1ABCDU);
}

TEST_F(OverrideBuiltinSystf, ADesignCallOfAnOverriddenDisplayRunsTheApp) {
  int calls = 0;
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$display");
  task.calltf = [](PLI_BYTE8* data) -> PLI_INT32 {
    ++*reinterpret_cast<int*>(data);
    return 0;
  };
  task.user_data = reinterpret_cast<PLI_BYTE8*>(&calls);
  ASSERT_NE(vpi_register_systf(&task), nullptr);
  SimFixture f;
  testing::internal::CaptureStdout();
  RunOverridden("  initial $display(\"built-in output\");\n", f);
  const std::string kOut = testing::internal::GetCapturedStdout();
  EXPECT_EQ(calls, 1);
  EXPECT_EQ(kOut.find("built-in output"), std::string::npos);
}

TEST_F(OverrideBuiltinSystf, AnOverriddenToolBuiltinRunsTheApp) {
  RegisterSizedOverride("$countdrivers", nullptr);
  SimFixture f;
  RunOverridden(
      "  wire w;\n"
      "  int r;\n"
      "  initial r = $countdrivers(w);\n",
      f);
  EXPECT_EQ(ValueAfterRun(f, "r"), 0x1ABCDU);
}

TEST_F(OverrideBuiltinSystf, AnOverriddenSignedTakesTheSizetfWidthAtEveryCall) {
  RegisterSizedOverride("$signed", SizeSeventeen);
  SimFixture f;
  RunOverridden(
      "  logic [39:0] r4, r8, r40;\n"
      "  initial begin\n"
      "    r4 = $signed(a4);\n"
      "    r8 = $signed(a8);\n"
      "    r40 = $signed(a40);\n"
      "  end\n",
      f);
  EXPECT_EQ(ValueAfterRun(f, "r4"), 0x1ABCDU);
  EXPECT_EQ(ValueAfterRun(f, "r8"), 0x1ABCDU);
  EXPECT_EQ(ValueAfterRun(f, "r40"), 0x1ABCDU);
}

TEST_F(OverrideBuiltinSystf,
       AnOverriddenUnsignedTakesTheSizetfWidthAtEveryCall) {
  RegisterSizedOverride("$unsigned", SizeSeventeen);
  SimFixture f;
  RunOverridden(
      "  logic [39:0] r4, r8;\n"
      "  logic [7:0] narrow;\n"
      "  initial begin\n"
      "    r4 = $unsigned(a4);\n"
      "    r8 = $unsigned(a8);\n"
      "    narrow = $unsigned(a40);\n"
      "  end\n",
      f);
  EXPECT_EQ(ValueAfterRun(f, "r4"), 0x1ABCDU);
  EXPECT_EQ(ValueAfterRun(f, "r8"), 0x1ABCDU);
  EXPECT_EQ(ValueAfterRun(f, "narrow"), 0xCDU);
}

TEST_F(OverrideBuiltinSystf, TheBitsOfAnOverriddenSignedCallIsTheSizetfWidth) {
  RegisterSizedOverride("$signed", SizeSeventeen);
  SimFixture f;
  RunOverridden(
      "  int b4, b40, bcat;\n"
      "  initial begin\n"
      "    b4 = $bits($signed(a4));\n"
      "    b40 = $bits($signed(a40));\n"
      "    bcat = $bits({$signed(a8), 1'b0});\n"
      "  end\n",
      f);
  EXPECT_EQ(ValueAfterRun(f, "b4"), 17U);
  EXPECT_EQ(ValueAfterRun(f, "b40"), 17U);
  EXPECT_EQ(ValueAfterRun(f, "bcat"), 18U);
}

int g_check_calls = 0;

PLI_INT32 CountCheckCall(PLI_BYTE8*) {
  ++g_check_calls;
  return 0;
}

void ExpectTimingCheckStands(const char* name, const std::string& check,
                             TimingCheckKind kind) {
  g_check_calls = 0;
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText(name);
  data.calltf = CountCheckCall;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top(\n"
      "    output logic d,\n"
      "    output logic clk);\n"
      "  specify\n"
      "    " +
          check +
          ";\n"
          "  endspecify\n"
          "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_EQ(g_check_calls, 0);
  const SpecifyManager* mgr = f.ctx.GetSpecifyManager();
  ASSERT_NE(mgr, nullptr);
  bool registered_as_a_check = false;
  for (const auto& entry : mgr->GetTimingChecks()) {
    if (entry.kind == kind) registered_as_a_check = true;
  }
  EXPECT_TRUE(registered_as_a_check);
}

TEST_F(OverrideBuiltinSystf, AHoldCheckCannotBeOverridden) {
  ExpectTimingCheckStands("$hold", "$hold(posedge clk, d, 3)",
                          TimingCheckKind::kHold);
}

TEST_F(OverrideBuiltinSystf, ASetupholdCheckCannotBeOverridden) {
  ExpectTimingCheckStands("$setuphold", "$setuphold(posedge clk, d, 1, 2)",
                          TimingCheckKind::kSetuphold);
}

TEST_F(OverrideBuiltinSystf, ARecoveryCheckCannotBeOverridden) {
  ExpectTimingCheckStands("$recovery", "$recovery(posedge clk, d, 3)",
                          TimingCheckKind::kRecovery);
}

TEST_F(OverrideBuiltinSystf, ARemovalCheckCannotBeOverridden) {
  ExpectTimingCheckStands("$removal", "$removal(posedge clk, d, 3)",
                          TimingCheckKind::kRemoval);
}

TEST_F(OverrideBuiltinSystf, ARecremCheckCannotBeOverridden) {
  ExpectTimingCheckStands("$recrem", "$recrem(posedge clk, d, 1, 2)",
                          TimingCheckKind::kRecrem);
}

TEST_F(OverrideBuiltinSystf, ASkewCheckCannotBeOverridden) {
  ExpectTimingCheckStands("$skew", "$skew(posedge clk, d, 3)",
                          TimingCheckKind::kSkew);
}

TEST_F(OverrideBuiltinSystf, ATimeskewCheckCannotBeOverridden) {
  ExpectTimingCheckStands("$timeskew", "$timeskew(posedge clk, d, 3)",
                          TimingCheckKind::kTimeskew);
}

TEST_F(OverrideBuiltinSystf, AFullskewCheckCannotBeOverridden) {
  ExpectTimingCheckStands("$fullskew", "$fullskew(posedge clk, d, 1, 2)",
                          TimingCheckKind::kFullskew);
}

TEST_F(OverrideBuiltinSystf, APeriodCheckCannotBeOverridden) {
  ExpectTimingCheckStands("$period", "$period(posedge clk, 5)",
                          TimingCheckKind::kPeriod);
}

TEST_F(OverrideBuiltinSystf, AWidthCheckCannotBeOverridden) {
  ExpectTimingCheckStands("$width", "$width(posedge clk, 5)",
                          TimingCheckKind::kWidth);
}

TEST_F(OverrideBuiltinSystf, ANochangeCheckCannotBeOverridden) {
  ExpectTimingCheckStands("$nochange", "$nochange(posedge clk, d, 0, 0)",
                          TimingCheckKind::kNochange);
}

}  // namespace
}  // namespace delta
