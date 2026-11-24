#include <gtest/gtest.h>

#include <algorithm>
#include <cctype>
#include <fstream>
#include <set>
#include <sstream>
#include <string>

#include "helpers_c_compiler.h"
#include "helpers_vpi_put_run.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

std::set<std::string> NamesNumberedInTheBaseFilesRange() {
  std::set<std::string> names;
  std::ifstream header(RepositoryRoot() / "src/simulator/sv_vpi_user.h");
  std::string line;
  while (std::getline(header, line)) {
    std::istringstream words(line);
    std::string directive;
    std::string name;
    std::string number;
    words >> directive >> name >> number;
    if (directive != "#define" || number.empty()) continue;
    if (!std::all_of(number.begin(), number.end(),
                     [](unsigned char c) { return std::isdigit(c); })) {
      continue;
    }
    int value = std::stoi(number);
    if (value >= 1 && value <= 299) names.insert(name);
  }
  return names;
}

TEST(VpiReservedConstants, OnlyTheReturnValuesOfTheSvFileFallInTheBaseRange) {
  EXPECT_EQ(NamesNumberedInTheBaseFilesRange(),
            (std::set<std::string>{"vpiJoinNone",
                                   "vpiJoinAny",
                                   "vpiForkJoinAcc",
                                   "vpiExternAcc",
                                   "vpiDPIExportAcc",
                                   "vpiDPIImportAcc",
                                   "vpiStaticArray",
                                   "vpiDynamicArray",
                                   "vpiAssocArray",
                                   "vpiQueueArray",
                                   "vpiNotRand",
                                   "vpiRand",
                                   "vpiRandC",
                                   "vpiInterfacePort",
                                   "vpiModportPort",
                                   "vpiPublicVis",
                                   "vpiProtectedVis",
                                   "vpiLocalVis",
                                   "vpiOneStepConst",
                                   "vpiUnboundedConst",
                                   "vpiNullConst",
                                   "vpiAlwaysComb",
                                   "vpiAlwaysFF",
                                   "vpiAlwaysLatch",
                                   "vpiEqualDist",
                                   "vpiDivDist",
                                   "vpiRef",
                                   "vpiMailboxClass",
                                   "vpiSemaphoreClass",
                                   "vpiUserDefinedClass",
                                   "vpiProcessClass",
                                   "vpiUniqueQualifier",
                                   "vpiPriorityQualifier",
                                   "vpiTaggedQualifier",
                                   "vpiRandQualifier",
                                   "vpiInsideQualifier",
                                   "vpiMode1364v1995",
                                   "vpiMode1364v2001",
                                   "vpiMode1364v2005",
                                   "vpiMode1800v2005",
                                   "vpiMode1800v2009",
                                   "vpiAutomaticScheme",
                                   "vpiDynamicScheme",
                                   "vpiOtherScheme",
                                   "vpiDPI",
                                   "vpiDPIC",
                                   "vpiImplyOp",
                                   "vpiNonOverlapImplyOp",
                                   "vpiOverlapImplyOp",
                                   "vpiAcceptOnOp",
                                   "vpiRejectOnOp",
                                   "vpiSyncAcceptOnOp",
                                   "vpiSyncRejectOnOp",
                                   "vpiOverlapFollowedByOp",
                                   "vpiNonOverlapFollowedByOp",
                                   "vpiNexttimeOp",
                                   "vpiAlwaysOp",
                                   "vpiEventuallyOp",
                                   "vpiUntilOp",
                                   "vpiUntilWithOp",
                                   "vpiUnaryCycleDelayOp",
                                   "vpiCycleDelayOp",
                                   "vpiIntersectOp",
                                   "vpiFirstMatchOp",
                                   "vpiThroughoutOp",
                                   "vpiWithinOp",
                                   "vpiRepeatOp",
                                   "vpiConsecutiveRepeatOp",
                                   "vpiGotoRepeatOp",
                                   "vpiPostIncOp",
                                   "vpiPreIncOp",
                                   "vpiPostDecOp",
                                   "vpiPreDecOp",
                                   "vpiMatchOp",
                                   "vpiCastOp",
                                   "vpiIffOp",
                                   "vpiWildEqOp",
                                   "vpiWildNeqOp",
                                   "vpiStreamLROp",
                                   "vpiStreamRLOp",
                                   "vpiMatchedOp",
                                   "vpiTriggeredOp",
                                   "vpiAssignmentPatternOp",
                                   "vpiMultiAssignmentPatternOp",
                                   "vpiIfOp",
                                   "vpiIfElseOp",
                                   "vpiCompAndOp",
                                   "vpiCompOrOp",
                                   "vpiImpliesOp",
                                   "vpiInsideOp",
                                   "vpiTypeOp",
                                   "vpiAssignmentOp",
                                   "vpiOtherFunc",
                                   "vpiValidUnknown"}));
}

class UnchangedValuePut : public VpiPutRun {
 protected:
  static void PutScalar(const char* name, PLI_INT32 scalar) {
    s_vpi_value value = {};
    value.format = vpiScalarVal;
    value.value.scalar = scalar;
    vpi_put_value(By(name), &value, nullptr, vpiNoDelay);
  }

  static void PutStrength(const char* name, PLI_INT32 logic) {
    s_vpi_strengthval strength = {logic, vpiStrongDrive, vpiStrongDrive};
    s_vpi_value value = {};
    value.format = vpiStrengthVal;
    value.value.strength = &strength;
    vpi_put_value(By(name), &value, nullptr, vpiNoDelay);
  }

  static PLI_INT32 ScalarOf(const char* name) {
    s_vpi_value value = {};
    value.format = vpiScalarVal;
    vpi_get_value(By(name), &value);
    return value.value.scalar;
  }
};

constexpr const char* kFourScalars =
    "module top;\n"
    "  logic zero = 0, one = 1, x = 1'bx, z = 1'bz;\n"
    "  initial $noop;\n"
    "endmodule\n";

TEST_F(UnchangedValuePut, ALogicLevelPutReplacesTheScalarsValue) {
  Run(kFourScalars);
  PutScalar("top.zero", vpi1);
  PutScalar("top.one", vpiX);
  PutScalar("top.x", vpiZ);
  PutStrength("top.z", vpi1);
  EXPECT_EQ(ScalarOf("top.zero"), vpi1);
  EXPECT_EQ(ScalarOf("top.one"), vpiX);
  EXPECT_EQ(ScalarOf("top.x"), vpiZ);
  EXPECT_EQ(ScalarOf("top.z"), vpi1);
}

TEST_F(UnchangedValuePut, DISABLED_ANoChangeScalarLeavesTheValueAsItWas) {
  Run(kFourScalars);
  for (const char* name : {"top.zero", "top.one", "top.x", "top.z"}) {
    PutScalar(name, vpiNoChange);
  }
  EXPECT_EQ(ScalarOf("top.zero"), vpi0);
  EXPECT_EQ(ScalarOf("top.one"), vpi1);
  EXPECT_EQ(ScalarOf("top.x"), vpiX);
  EXPECT_EQ(ScalarOf("top.z"), vpiZ);
}

TEST_F(UnchangedValuePut, DISABLED_ANoChangeStrengthLeavesTheValueAsItWas) {
  Run(kFourScalars);
  for (const char* name : {"top.zero", "top.one", "top.x", "top.z"}) {
    PutStrength(name, vpiNoChange);
  }
  EXPECT_EQ(ScalarOf("top.zero"), vpi0);
  EXPECT_EQ(ScalarOf("top.one"), vpi1);
  EXPECT_EQ(ScalarOf("top.x"), vpiX);
  EXPECT_EQ(ScalarOf("top.z"), vpiZ);
}

}  // namespace
}  // namespace delta
