#include <gtest/gtest.h>

#include <vector>

#include "fixture_simulator.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiVariablesClass : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  std::vector<vpiHandle> ScanAll(vpiHandle it) {
    std::vector<vpiHandle> seen;
    if (it == nullptr) return seen;
    while (vpiHandle h = vpi_scan(it)) seen.push_back(h);
    return seen;
  }

  VpiContext vpi_ctx_;
};

TEST_F(VpiVariablesClass, TheRelationReachesEveryKindTheClassGroups) {
  VpiObject logic_var;
  logic_var.type = vpiLogicVar;
  VpiObject int_var;
  int_var.type = vpiIntVar;
  VpiObject string_var;
  string_var.type = vpiStringVar;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&logic_var, &int_var, &string_var};

  std::vector<vpiHandle> seen =
      ScanAll(vpi_iterate(vpiVariables, VpiHandleOf(&scope)));
  ASSERT_EQ(seen.size(), 3u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &logic_var);
  EXPECT_EQ(VpiObjectOf(seen[1]), &int_var);
  EXPECT_EQ(VpiObjectOf(seen[2]), &string_var);
}

TEST_F(VpiVariablesClass, TheClassConstantIsNotAKindTheRelationReports) {
  VpiObject tagged_with_the_class;
  tagged_with_the_class.type = vpiVariables;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&tagged_with_the_class};

  EXPECT_TRUE(ScanAll(vpi_iterate(vpiVariables, VpiHandleOf(&scope))).empty());
}

TEST_F(VpiVariablesClass, AGroupedObjectReportsItsOwnDefinitionAsItsType) {
  VpiObject int_var;
  int_var.type = vpiIntVar;

  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&int_var)), vpiIntVar);
  EXPECT_NE(vpi_get(vpiType, VpiHandleOf(&int_var)), vpiVariables);
}

TEST_F(VpiVariablesClass, AnObjectOutsideTheEnclosureIsNotReached) {
  VpiObject net;
  net.type = kVpiNet;
  VpiObject logic_var;
  logic_var.type = vpiLogicVar;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&net, &logic_var};

  std::vector<vpiHandle> seen =
      ScanAll(vpi_iterate(vpiVariables, VpiHandleOf(&scope)));
  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &logic_var);
}

int g_vars_seen = 0;

PLI_INT32 CountVariablesCalltf(PLI_BYTE8*) {
  vpiHandle mod = vpi_handle_by_name(VpiText("m1"), nullptr);
  if (mod == nullptr) return 0;
  vpiHandle itr = vpi_iterate(vpiVariables, mod);
  if (itr == nullptr) return 0;
  while (vpi_scan(itr) != nullptr) ++g_vars_seen;
  return 0;
}

void RegisterVariableCountProbe() {
  g_vars_seen = 0;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &CountVariablesCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

TEST_F(VpiVariablesClass, AScopeOfADesignReachesTheVariablesItDeclares) {
  RegisterVariableCountProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  reg b;\n"
      "endmodule\n"
      "module t;\n"
      "  m m1();\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_vars_seen, 2);
}

}  // namespace
}  // namespace delta
