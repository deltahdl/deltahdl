#include <gtest/gtest.h>

// §36.12.2: "In order to ease the transition to the latest VPI standard for
// older applications, capability shall be provided to emulate the incompatible
// VPI behaviors where they conflict with the current standard. This allows
// older VPI applications dependent on these behaviors to be run unmodified...
// As described in 36.12.2.1 and 36.12.2.2, two mechanisms to support this shall
// be provided, which can be used in combination."
//
// This translation unit is such an older application: it selects a
// compatibility version before the VPI headers, exactly as §36.12.2.1's
// mechanism prescribes, and then calls the VPI as it always did. The selection
// renames every call, so the capability is provided only if those names resolve
// - and only if what they do is the behavior of the version selected.
#define VPI_COMPATIBILITY_VERSION_1364v2001 1

// clang-format off
// The mechanism's header is read before the VPI headers, and stays there: it
// is the selection that renames the entry points, so the declarations below
// have to be read after it. Sorted in with them it lands last, the prototypes
// are emitted under their plain names, and only the calls are renamed.
#include "simulator/vpi_compatibility.h"
// clang-format on

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

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

// §36.12.1 Table 36-10 row 5 is N for IEEE Std 1364-2001: "In all IEEE Std 1364
// standards, vpiReg and vpiRegArray objects were excluded from vpiVariables
// iterations." An application built against that standard is handed the
// iteration it expects, without the two kinds this standard added to it.
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

  std::vector<vpiHandle> seen = ScanAll(vpi_iterate(vpiVariables, &scope));
  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(seen[0], &int_var);
}

// Row 6 is N for the same standard: a vpiReg iteration on an array retrieves
// the reg elements and nothing else, the elements of other kinds "not expected
// in IEEE Std 1364-2001".
TEST_F(VpiCompatibilityEmulation, ARegIterationOnAnArrayRetrievesOnlyRegs) {
  VpiObject reg_word;
  reg_word.type = vpiReg;
  VpiObject int_word;
  int_word.type = vpiIntegerVar;

  VpiObject array;
  array.type = vpiRegArray;
  array.children = {&reg_word, &int_word};

  std::vector<vpiHandle> seen = ScanAll(vpi_iterate(vpiReg, &array));
  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(seen[0], &reg_word);
}

// Row 7 is N for the same standard: "IEEE Std 1364-2001 and IEEE Std 1364-2005,
// vpiRegArray iterations only included arrays of vpiReg objects", so an array
// of some other variable is not among them.
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

  std::vector<vpiHandle> seen = ScanAll(vpi_iterate(vpiRegArray, &scope));
  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(seen[0], &reg_array);
}

// An iteration the emulation empties reaches no object, which §38.23 reports as
// no iterator rather than one that scans to nothing on its first call.
TEST_F(VpiCompatibilityEmulation, AnIterationLeftWithNothingIsNoIterator) {
  VpiObject reg;
  reg.type = vpiReg;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&reg};

  EXPECT_EQ(vpi_iterate(vpiVariables, &scope), nullptr);
}

// The rest of the interface is the current one. The mechanism renames every
// entry point, so each of the others has to resolve too, and what they do is
// unchanged - a mode selection emulates the behaviors that differ and no other.
TEST_F(VpiCompatibilityEmulation, TheOtherEntryPointsResolveAndAreUnchanged) {
  VpiObject mod;
  mod.type = vpiModule;
  mod.name = "top";
  VpiObject port;
  port.type = vpiPort;
  port.parent = &mod;
  mod.children = {&port};

  EXPECT_EQ(vpi_get(vpiType, &mod), vpiModule);
  EXPECT_STREQ(vpi_get_str(vpiName, &mod), "top");
  EXPECT_EQ(vpi_handle(vpiModule, &port), &mod);
  EXPECT_EQ(vpi_compare_objects(&mod, &mod), 1);
}

}  // namespace
}  // namespace delta
