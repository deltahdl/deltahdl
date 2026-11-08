#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

std::vector<std::string> g_reached;
const char* g_probe_user_data_seen = nullptr;

char g_probe_user_data[] = "probe-data";
char g_other_user_data[] = "other-data";

PLI_INT32 ProbeCompiletf(PLI_BYTE8* user_data) {
  g_reached.emplace_back("probe-compiletf");
  g_probe_user_data_seen = user_data;
  return 0;
}

PLI_INT32 ProbeCalltf(PLI_BYTE8* user_data) {
  g_reached.emplace_back("probe-calltf");
  g_probe_user_data_seen = user_data;
  return 0;
}

PLI_INT32 OtherCompiletf(PLI_BYTE8*) {
  g_reached.emplace_back("other-compiletf");
  return 0;
}

PLI_INT32 OtherCalltf(PLI_BYTE8*) {
  g_reached.emplace_back("other-calltf");
  return 0;
}

void RegisterProbe() {
  s_vpi_systf_data data = {};
  data.type = vpiSysFunc;
  data.sysfunctype = vpiIntFunc;
  data.tfname = VpiText("$probe");
  data.compiletf = &ProbeCompiletf;
  data.calltf = &ProbeCalltf;
  data.user_data = g_probe_user_data;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

void RegisterOther() {
  s_vpi_systf_data data = {};
  data.type = vpiSysFunc;
  data.sysfunctype = vpiIntFunc;
  data.tfname = VpiText("$other");
  data.compiletf = &OtherCompiletf;
  data.calltf = &OtherCalltf;
  data.user_data = g_other_user_data;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

class PliMechanism : public ::testing::Test {
 protected:
  void SetUp() override {
    g_reached.clear();
    g_probe_user_data_seen = nullptr;
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(PliMechanism,
       TheNameInTheSourceReachesApplicationsForMoreThanOneReason) {
  RegisterProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  initial r = $probe();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_reached,
            (std::vector<std::string>{"probe-compiletf", "probe-calltf"}));
}

TEST_F(PliMechanism, TheRoutinesAndTheDataComeFromTheRegistrationOfThatName) {
  RegisterProbe();
  RegisterOther();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  initial r = $probe();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_reached,
            (std::vector<std::string>{"probe-compiletf", "probe-calltf"}));
  EXPECT_EQ(g_probe_user_data_seen, g_probe_user_data);
}

TEST_F(PliMechanism, ANameEncounteredInADeclarationReachesItsApplications) {
  RegisterProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r = $probe();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(std::count(g_reached.begin(), g_reached.end(), "probe-compiletf"),
            1);
  EXPECT_EQ(std::count(g_reached.begin(), g_reached.end(), "probe-calltf"), 1);
}

}  // namespace
}  // namespace delta
