#include <gtest/gtest.h>

#include "simulator/vpi_globals.h"

#define VPI_COMPATIBILITY_VERSION_1364v2001 1

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiCompatibilityEmulation : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  std::vector<vpiHandle> ScanAll(vpiHandle it) {
    std::vector<vpiHandle> seen;
    if (it == nullptr) return seen;
    while (vpiHandle h = vpi_scan(it)) seen.push_back(h);
    return seen;
  }

  VpiContext ctx_;
};

TEST_F(VpiCompatibilityEmulation, AVariablesIterationExcludesRegsAndRegArrays) {
  VpiObject reg;
  reg.type = vpiReg;
  VpiObject int_var;
  int_var.type = vpiIntVar;
  VpiObject array;
  array.type = vpiRegArray;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&reg, &int_var, &array};

  std::vector<vpiHandle> seen =
      ScanAll(vpi_iterate(vpiVariables, VpiHandleOf(&scope)));
  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &int_var);
}

TEST_F(VpiCompatibilityEmulation, ARegIterationOnAnArrayRetrievesOnlyRegs) {
  VpiObject reg_word;
  reg_word.type = vpiReg;
  VpiObject int_word;
  int_word.type = vpiIntegerVar;

  VpiObject array;
  array.type = vpiRegArray;
  array.children = {&reg_word, &int_word};

  std::vector<vpiHandle> seen =
      ScanAll(vpi_iterate(vpiReg, VpiHandleOf(&array)));
  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &reg_word);
}

TEST_F(VpiCompatibilityEmulation, ARegArrayIterationReachesOnlyArraysOfRegs) {
  VpiObject reg_word;
  reg_word.type = vpiReg;
  VpiObject reg_array;
  reg_array.type = vpiRegArray;
  reg_array.children = {&reg_word};

  VpiObject int_word;
  int_word.type = vpiIntegerVar;
  VpiObject int_array;
  int_array.type = vpiRegArray;
  int_array.children = {&int_word};

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&reg_array, &int_array};

  std::vector<vpiHandle> seen =
      ScanAll(vpi_iterate(vpiRegArray, VpiHandleOf(&scope)));
  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &reg_array);
}

TEST_F(VpiCompatibilityEmulation, AnIterationLeftWithNothingIsNoIterator) {
  VpiObject reg;
  reg.type = vpiReg;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&reg};

  EXPECT_EQ(vpi_iterate(vpiVariables, VpiHandleOf(&scope)), nullptr);
}

TEST_F(VpiCompatibilityEmulation, TheOtherEntryPointsResolveAndAreUnchanged) {
  VpiObject mod;
  mod.type = vpiModule;
  mod.name = "top";
  VpiObject port;
  port.type = vpiPort;
  port.parent = &mod;
  mod.children = {&port};

  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&mod)), vpiModule);
  EXPECT_STREQ(vpi_get_str(vpiName, VpiHandleOf(&mod)), "top");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, VpiHandleOf(&port))), &mod);
  EXPECT_EQ(vpi_compare_objects(VpiHandleOf(&mod), VpiHandleOf(&mod)), 1);
}

}  // namespace
}  // namespace delta
