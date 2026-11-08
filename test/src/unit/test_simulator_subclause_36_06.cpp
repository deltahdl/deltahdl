#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

int g_seen = 0;

PLI_INT32 ReadRCalltf(PLI_BYTE8*) {
  s_vpi_value val = {};
  val.format = vpiIntVal;
  vpi_get_value(vpi_handle_by_name(VpiText("r"), nullptr), &val);
  g_seen = val.value.integer;
  return 0;
}

PLI_INT32 WriteRCalltf(PLI_BYTE8*) {
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 42;
  vpi_put_value(vpi_handle_by_name(VpiText("r"), nullptr), &val, nullptr,
                vpiNoDelay);
  return 0;
}

void RegisterProbe(PLI_INT32 (*calltf)(PLI_BYTE8*)) {
  g_seen = 0;
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = calltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

class PliApplicationDesignAccess : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(PliApplicationDesignAccess, TheApplicationReadsTheDesignAsItRuns) {
  RegisterProbe(&ReadRCalltf);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  initial begin\n"
      "    r = 7;\n"
      "    $probe;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_seen, 7);
}

TEST_F(PliApplicationDesignAccess, TheApplicationWritesWhereTheDesignReads) {
  RegisterProbe(&WriteRCalltf);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  int after;\n"
      "  initial begin\n"
      "    r = 1;\n"
      "    $probe;\n"
      "    after = r;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* after = f.ctx.FindVariable("after");
  ASSERT_NE(after, nullptr);
  EXPECT_EQ(after->value.ToUint64(), 42u);
}

TEST_F(PliApplicationDesignAccess, ARunWithNoApplicationAttachesNothing) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  initial r = 7;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(vpi_handle_by_name(VpiText("r"), nullptr), nullptr);
}

}  // namespace
}  // namespace delta
