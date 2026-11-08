#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

std::string g_net_name;
std::string g_net_full_name;
std::string g_module_full_name;
int g_net_size = 0;
int g_net_vector = -1;
int g_net_type = 0;
int g_module_type = 0;
int g_nets_scanned = 0;
bool g_iteration_found_the_net = false;

PLI_INT32 ReadFigureOneCalltf(PLI_BYTE8*) {
  vpiHandle net = vpi_handle_by_name(VpiText("t.m1.w"), nullptr);
  if (net == nullptr) return 0;
  vpiHandle mod = vpi_handle(vpiModule, net);
  if (mod == nullptr) return 0;

  g_net_type = vpi_get(vpiType, net);
  g_module_type = vpi_get(vpiType, mod);

  g_net_vector = vpi_get(vpiVector, net);
  g_net_size = vpi_get(vpiSize, net);
  if (const char* name = vpi_get_str(vpiName, net)) g_net_name = name;
  if (const char* full = vpi_get_str(vpiFullName, net)) g_net_full_name = full;
  if (const char* full = vpi_get_str(vpiFullName, mod)) {
    g_module_full_name = full;
  }

  vpiHandle itr = vpi_iterate(vpiNet, mod);
  if (itr == nullptr) return 0;
  while (vpiHandle scanned = vpi_scan(itr)) {
    ++g_nets_scanned;
    if (vpi_compare_objects(scanned, net) != 0) {
      g_iteration_found_the_net = true;
    }
  }
  return 0;
}

class VpiDataModelDiagramKeys : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    g_net_name.clear();
    g_net_full_name.clear();
    g_module_full_name.clear();
    g_net_size = 0;
    g_net_vector = -1;
    g_net_type = 0;
    g_module_type = 0;
    g_nets_scanned = 0;
    g_iteration_found_the_net = false;
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
};

TEST_F(VpiDataModelDiagramKeys, FigureOneIsReadByTheThreeKeys) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &ReadFigureOneCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [7:0] w;\n"
      "  assign w = 8'h5a;\n"
      "endmodule\n"
      "module t;\n"
      "  m m1();\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_net_type, vpiNet);
  EXPECT_EQ(g_module_type, vpiModule);

  EXPECT_EQ(g_net_name, "w");
  EXPECT_EQ(g_net_full_name, "t.m1.w");
  EXPECT_EQ(g_net_size, 8);
  EXPECT_EQ(g_net_vector, 1);
  EXPECT_EQ(g_module_full_name, "t.m1");

  EXPECT_GT(g_nets_scanned, 0);
  EXPECT_TRUE(g_iteration_found_the_net);
}

}  // namespace
}  // namespace delta
