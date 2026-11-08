#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class SystfTypes : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

int g_dual_calls = 0;

PLI_INT32 DualCalltf(PLI_BYTE8*) {
  ++g_dual_calls;
  return 0;
}

void RunDual(int type, const std::string& src, SimFixture& f) {
  s_vpi_systf_data data = {};
  data.type = type;
  data.sysfunctype = vpiSizedFunc;
  data.tfname = VpiText("$dual");
  data.calltf = DualCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

constexpr const char* kDualAsAnOperand =
    "module t;\n"
    "  int r;\n"
    "  initial r = $dual();\n"
    "endmodule\n";

TEST_F(SystfTypes, ATaskTypedRegistrationIsRefusedWhereAValueIsWanted) {
  g_dual_calls = 0;
  SimFixture f;
  RunDual(vpiSysTask, kDualAsAnOperand, f);

  EXPECT_EQ(g_dual_calls, 0);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dual is a user-defined system task and returns "
                            "no value, so it cannot be used as an expression",
                            3, "36.5"));
}

TEST_F(SystfTypes, AFunctionTypedRegistrationIsCalledWhereAValueIsWanted) {
  g_dual_calls = 0;
  SimFixture f;
  RunDual(vpiSysFunc, kDualAsAnOperand, f);

  EXPECT_EQ(g_dual_calls, 1);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST_F(SystfTypes, ATaskTypedRegistrationIsCalledWhereAStatementStands) {
  g_dual_calls = 0;
  SimFixture f;
  RunDual(vpiSysTask,
          "module t;\n"
          "  initial $dual;\n"
          "endmodule\n",
          f);

  EXPECT_EQ(g_dual_calls, 1);
  EXPECT_FALSE(f.diag.HasErrors());
}

int g_put_error_level = 0;

PLI_INT32 PutThroughTheCallCalltf(PLI_BYTE8*) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 42;
  vpi_put_value(vpi_handle(vpiSysTfCall, nullptr), &value, nullptr, vpiNoDelay);
  g_put_error_level = vpi_chk_error(nullptr);
  return 0;
}

TEST_F(SystfTypes, ATaskCallRefusesAValuePutThroughIt) {
  g_put_error_level = 0;
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$put_from_task");
  data.calltf = PutThroughTheCallCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $put_from_task;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_put_error_level, vpiError);
}

}  // namespace
}  // namespace delta
