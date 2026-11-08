#include <gtest/gtest.h>

#include <cstdint>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "fixture_simulator.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

bool g_m1_found = false;
bool g_m2_found = false;
bool g_wire_found = false;
int g_same_object = -1;
int g_wire_type = 0;
uint64_t g_m1_value = 0;
uint64_t g_m2_value = 0;

PLI_INT32 InspectCalltf(PLI_BYTE8*) {
  vpiHandle m1_r = vpi_handle_by_name(VpiText("m1.r"), nullptr);
  vpiHandle m2_r = vpi_handle_by_name(VpiText("m2.r"), nullptr);
  g_m1_found = m1_r != nullptr;
  g_m2_found = m2_r != nullptr;

  vpiHandle m1_w = vpi_handle_by_name(VpiText("m1.w"), nullptr);
  g_wire_found = m1_w != nullptr;
  if (m1_w != nullptr) g_wire_type = vpi_get(vpiType, m1_w);

  if (m1_r == nullptr || m2_r == nullptr) return 0;
  g_same_object = vpi_compare_objects(m1_r, m2_r);

  s_vpi_value put = {};
  put.format = vpiIntVal;
  put.value.integer = 42;
  vpi_put_value(m1_r, &put, nullptr, vpiNoDelay);

  s_vpi_value got = {};
  got.format = vpiIntVal;
  vpi_get_value(m1_r, &got);
  g_m1_value = static_cast<uint64_t>(got.value.integer);
  vpi_get_value(m2_r, &got);
  g_m2_value = static_cast<uint64_t>(got.value.integer);
  return 0;
}

void RegisterProbe() {
  g_m1_found = false;
  g_m2_found = false;
  g_wire_found = false;
  g_same_object = -1;
  g_wire_type = 0;
  g_m1_value = 0;
  g_m2_value = 0;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &InspectCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

void RunTwoInstances(SimFixture& f) {
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  int r;\n"
      "endmodule\n"
      "module t;\n"
      "  m m1();\n"
      "  m m2();\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

class InstantiatedDesignAccess : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(InstantiatedDesignAccess, EachInstanceIsReachedUnderItsOwnName) {
  RegisterProbe();

  SimFixture f;
  RunTwoInstances(f);

  EXPECT_TRUE(g_m1_found);
  EXPECT_TRUE(g_m2_found);
  EXPECT_EQ(g_same_object, 0);
}

TEST_F(InstantiatedDesignAccess, EachInstanceCarriesItsOwnValue) {
  RegisterProbe();

  SimFixture f;
  RunTwoInstances(f);

  ASSERT_TRUE(g_m1_found);
  ASSERT_TRUE(g_m2_found);
  EXPECT_EQ(g_m1_value, 42u);
  EXPECT_EQ(g_m2_value, 0u);
}

TEST_F(InstantiatedDesignAccess, TheClausesOwnExampleObjectIsAWire) {
  RegisterProbe();

  SimFixture f;
  RunTwoInstances(f);

  EXPECT_TRUE(g_wire_found);
  EXPECT_EQ(g_wire_type, vpiNet);
}

TEST(DesignWalk, AGenerateBlockPathStopsAtAStepThatFindsNothing) {
  VpiObject instance;
  instance.type = vpiModule;
  const HierPath kPath = {HierStep{"g", false, 0, "g", {}},
                          HierStep{"h", false, 0, "h", {}}};
  EXPECT_EQ(VpiGenScopeOf(&instance, kPath), nullptr);
}

TEST(DesignWalk, AttachPassesOverInstancesWithNothingToVisit) {
  for (int which = 0; which < 4; ++which) {
    VpiContext vpi_ctx;
    SetGlobalVpiContext(&vpi_ctx);
    SimFixture f;
    RtlirModule unnamed;
    unnamed.children.resize(1);
    RtlirModule dotted;
    dotted.name = "x.y";
    dotted.variables.resize(1);
    dotted.variables.front().name = "unbuilt";
    RtlirDesign design;
    if (which == 1) design.top_modules = {nullptr};
    if (which == 2) design.top_modules = {&unnamed, &dotted};
    if (which == 3) design.top_modules = {&dotted};
    vpi_ctx.Attach(f.ctx, &design);
    if (which < 2) EXPECT_EQ(vpi_iterate(vpiModule, nullptr), nullptr);
    SetGlobalVpiContext(nullptr);
  }
}

}  // namespace
}  // namespace delta
