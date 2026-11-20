#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
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

class InstancesOfARun : public VpiDesignRun {
 protected:
  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = -1;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }

  static std::string FullNameOf(vpiHandle obj) {
    const char* name = obj == nullptr ? nullptr : vpi_get_str(vpiFullName, obj);
    return name == nullptr ? "" : name;
  }

  static void ExpectEachInItsOwnScope(vpiHandle one, vpiHandle two,
                                      const std::string& first,
                                      const std::string& second, int relation) {
    vpiHandle one_scope = vpi_handle(relation, one);
    vpiHandle two_scope = vpi_handle(relation, two);
    ASSERT_NE(one_scope, nullptr);
    ASSERT_NE(two_scope, nullptr);
    EXPECT_EQ(vpi_compare_objects(one_scope, two_scope), 0);
    EXPECT_EQ(FullNameOf(one_scope), first.substr(0, first.rfind('.')));
    EXPECT_EQ(FullNameOf(two_scope), second.substr(0, second.rfind('.')));
  }

  static void ExpectTwoSeparateObjects(const char* first, const char* second,
                                       int relation, int type,
                                       std::pair<int, int> values) {
    vpiHandle one = vpi_handle_by_name(VpiText(first), nullptr);
    vpiHandle two = vpi_handle_by_name(VpiText(second), nullptr);
    ASSERT_NE(one, nullptr);
    ASSERT_NE(two, nullptr);
    EXPECT_EQ(vpi_get(vpiType, one), type);
    EXPECT_EQ(vpi_get(vpiType, two), type);
    EXPECT_EQ(vpi_compare_objects(one, two), 0);
    EXPECT_EQ(IntOf(one), values.first);
    EXPECT_EQ(IntOf(two), values.second);
    EXPECT_EQ(FullNameOf(one), first);
    EXPECT_EQ(FullNameOf(two), second);
    ExpectEachInItsOwnScope(one, two, first, second, relation);
  }
};

constexpr const char* kTwoModuleInstances =
    "module m(input logic [31:0] d);\n"
    "  wire [31:0] w;\n"
    "  assign w = d;\n"
    "  int r;\n"
    "  initial r = d + 10;\n"
    "endmodule\n"
    "module t;\n"
    "  m m1(1);\n"
    "  m m2(2);\n"
    "  initial $noop;\n"
    "endmodule\n";

TEST_F(InstancesOfARun, EachInstanceOfTheClausesNetIsItsOwnObject) {
  Run(kTwoModuleInstances);
  ExpectTwoSeparateObjects("t.m1.w", "t.m2.w", vpiModule, vpiNet, {1, 2});
}

TEST_F(InstancesOfARun, EachInstanceOfAModuleVariableIsItsOwnObject) {
  Run(kTwoModuleInstances);
  ExpectTwoSeparateObjects("t.m1.r", "t.m2.r", vpiModule, vpiIntVar, {11, 12});
}

TEST_F(InstancesOfARun, EachInstanceOfAnInterfaceVariableIsItsOwnObject) {
  Run("interface i(input logic [31:0] d);\n"
      "  int r;\n"
      "  initial r = d + 20;\n"
      "endinterface\n"
      "module t;\n"
      "  i i1(1);\n"
      "  i i2(2);\n"
      "  initial $noop;\n"
      "endmodule\n");
  ExpectTwoSeparateObjects("t.i1.r", "t.i2.r", vpiScope, vpiIntVar, {21, 22});
}

TEST_F(InstancesOfARun, EachInstanceOfAProgramVariableIsItsOwnObject) {
  Run("program p(input logic [31:0] d);\n"
      "  int r;\n"
      "  initial r = d + 30;\n"
      "endprogram\n"
      "module t;\n"
      "  p p1(1);\n"
      "  p p2(2);\n"
      "  initial $noop;\n"
      "endmodule\n");
  ExpectTwoSeparateObjects("t.p1.r", "t.p2.r", vpiScope, vpiIntVar, {31, 32});
}

}  // namespace
}  // namespace delta
