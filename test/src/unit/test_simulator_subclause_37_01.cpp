#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

int g_tops_seen = 0;
std::string g_top_name;
int g_top_is_top = 0;
bool g_reached_instance = false;
bool g_reached_net = false;
int g_instance_is_top = 0;

PLI_INT32 WalkFromTheTopCalltf(PLI_BYTE8*) {
  vpiHandle tops = vpi_iterate(vpiModule, nullptr);
  if (tops == nullptr) return 0;
  vpiHandle top = nullptr;
  while (vpiHandle next = vpi_scan(tops)) {
    ++g_tops_seen;
    top = next;
  }
  if (top == nullptr) return 0;

  const char* name = vpi_get_str(vpiName, top);
  if (name != nullptr) g_top_name = name;
  g_top_is_top = vpi_get(vpiTopModule, top);

  vpiHandle instances = vpi_iterate(vpiModule, top);
  if (instances != nullptr) {
    while (vpiHandle instance = vpi_scan(instances)) {
      g_reached_instance = true;
      g_instance_is_top = vpi_get(vpiTopModule, instance);
      vpiHandle nets = vpi_iterate(vpiNet, instance);
      if (nets == nullptr) continue;
      while (vpi_scan(nets) != nullptr) g_reached_net = true;
    }
  }
  return 0;
}

void RegisterWalkProbe() {
  g_tops_seen = 0;
  g_top_name.clear();
  g_top_is_top = 0;
  g_reached_instance = false;
  g_reached_net = false;
  g_instance_is_top = 0;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &WalkFromTheTopCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

class UsingTheDataModel : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(UsingTheDataModel, AnApplicationReachesTheDesignsTopModule) {
  RegisterWalkProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "endmodule\n"
      "module t;\n"
      "  m m1();\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_tops_seen, 1);
  EXPECT_EQ(g_top_name, "t");
  EXPECT_EQ(g_top_is_top, 1);
}

TEST_F(UsingTheDataModel, TheWalkGoesDownFromTheTop) {
  RegisterWalkProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "endmodule\n"
      "module t;\n"
      "  m m1();\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_TRUE(g_reached_instance);
  EXPECT_TRUE(g_reached_net);
  EXPECT_EQ(g_instance_is_top, 0);
}

}  // namespace
}  // namespace delta
