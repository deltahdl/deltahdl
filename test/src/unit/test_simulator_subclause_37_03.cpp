#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

int g_nets_from_module = 0;
int g_nets_reaching_back = 0;
std::string g_bus_name;
int g_bus_size = 0;
int g_bus_vector = -1;
int g_scalar_vector = -1;
int g_module_scalar = -1;
int g_module_vector = -1;

PLI_INT32 WalkModuleNetsCalltf(PLI_BYTE8*) {
  vpiHandle mod = vpi_handle_by_name(VpiText("m1"), nullptr);
  if (mod == nullptr) return 0;
  g_module_scalar = vpi_get(vpiScalar, mod);
  g_module_vector = vpi_get(vpiVector, mod);

  vpiHandle nets = vpi_iterate(vpiNet, mod);
  if (nets == nullptr) return 0;
  for (vpiHandle net = vpi_scan(nets); net != nullptr; net = vpi_scan(nets)) {
    ++g_nets_from_module;

    if (vpi_compare_objects(vpi_handle(vpiModule, net), mod) == 1) {
      ++g_nets_reaching_back;
    }

    const char* name = vpi_get_str(vpiName, net);
    int size = vpi_get(vpiSize, net);
    int vector = vpi_get(vpiVector, net);
    if (name != nullptr && std::string(name) == "bus") {
      g_bus_name = name;
      g_bus_size = size;
      g_bus_vector = vector;
    } else {
      g_scalar_vector = vector;
    }
  }
  return 0;
}

void RegisterFigureProbe() {
  g_nets_from_module = 0;
  g_nets_reaching_back = 0;
  g_bus_name.clear();
  g_bus_size = 0;
  g_bus_vector = -1;
  g_scalar_vector = -1;
  g_module_scalar = -1;
  g_module_vector = -1;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &WalkModuleNetsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

void RunModuleWithTwoNets(SimFixture& f) {
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  wire [7:0] bus;\n"
      "endmodule\n"
      "module t;\n"
      "  m m1();\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

class VpiObjectClassifications : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(VpiObjectClassifications, BothRelationsOfTheFigureAreTraversable) {
  RegisterFigureProbe();

  SimFixture f;
  RunModuleWithTwoNets(f);

  EXPECT_EQ(g_nets_from_module, 2);
  EXPECT_EQ(g_nets_reaching_back, 2);
}

TEST_F(VpiObjectClassifications, TheThreePropertiesOfANetAreAnswered) {
  RegisterFigureProbe();

  SimFixture f;
  RunModuleWithTwoNets(f);

  EXPECT_EQ(g_bus_name, "bus");
  EXPECT_EQ(g_bus_size, 8);
  EXPECT_EQ(g_bus_vector, 1);
  EXPECT_EQ(g_scalar_vector, 0);
}

TEST_F(VpiObjectClassifications, TheModuleIsNeitherScalarNorVector) {
  RegisterFigureProbe();

  SimFixture f;
  RunModuleWithTwoNets(f);

  EXPECT_EQ(g_module_scalar, 0);
  EXPECT_EQ(g_module_vector, 0);
}

}  // namespace
}  // namespace delta
