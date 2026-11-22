#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

constexpr const char* kForms =
    "package pkg; timeunit 10ns; timeprecision 1ps; parameter D = 7;\n"
    "endpackage\n"
    "module top; timeunit 10ns; timeprecision 1ps;\n"
    "  parameter P = 4; int a, b, d = 2;\n"
    "  initial #1 begin a = 1; end\n"
    "  initial #1 #2 a = 2;\n"
    "  always #3 a = 3;\n"
    "  initial fork #4 a = 4; join\n"
    "  initial forever begin #5 a = 5; end\n"
    "  initial repeat (2) #6 a = 6;\n"
    "  initial #(1:2:3) a = 7;\n"
    "  initial #P a = 8;\n"
    "  initial #pkg::D a = 9;\n"
    "  initial #5ns a = 10;\n"
    "  initial #1.5 a = 11;\n"
    "  initial #0 a = 12;\n"
    "  initial #d a = 13;\n"
    "  initial a = #5 b;\n"
    "  initial a <= #5 b;\n"
    "  initial a = #d b;\n"
    "  initial a = #(1:2:3) b;\n"
    "  initial #100 $finish;\n"
    "endmodule\n";

class DelayControlsEverywhere : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Run(kForms);
  }

  static vpiHandle BodyOf(size_t n) {
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
    return n < kProcs.size() ? vpi_handle(vpiStmt, kProcs[n]) : nullptr;
  }

  static vpiHandle IntraControlOf(size_t n) {
    vpiHandle assign = BodyOf(n);
    return assign == nullptr ? nullptr : vpi_handle(vpiDelayControl, assign);
  }

  static vpiHandle DelayOf(size_t n) {
    vpiHandle control = BodyOf(n);
    return control == nullptr ? nullptr : vpi_handle(vpiDelay, control);
  }

  static uint64_t SimDelayOf(vpiHandle control) {
    s_vpi_time slot = {};
    s_vpi_delay delay = {};
    delay.da = &slot;
    delay.no_of_delays = 1;
    delay.time_type = vpiSimTime;
    vpi_get_delays(control, &delay);
    return (static_cast<uint64_t>(slot.high) << 32) | slot.low;
  }

  static void ExpectGuarded(vpiHandle control, int type) {
    ASSERT_NE(control, nullptr);
    EXPECT_EQ(vpi_get(vpiType, control), vpiDelayControl);
    vpiHandle guarded = vpi_handle(vpiStmt, control);
    ASSERT_NE(guarded, nullptr);
    EXPECT_EQ(vpi_get(vpiType, guarded), type);
  }
};

TEST_F(DelayControlsEverywhere, ADelayedBlockIsTheStmt) {
  ExpectGuarded(BodyOf(0), vpiBegin);
}

TEST_F(DelayControlsEverywhere, ADelayedDelayControlIsTheStmt) {
  vpiHandle outer = BodyOf(1);
  ExpectGuarded(outer, vpiDelayControl);
  ExpectGuarded(vpi_handle(vpiStmt, outer), vpiAssignment);
}

TEST_F(DelayControlsEverywhere, AnAlwaysDelaysItsAssignment) {
  ExpectGuarded(BodyOf(2), vpiAssignment);
}

TEST_F(DelayControlsEverywhere, ADelayInsideAForkDelaysItsAssignment) {
  const std::vector<vpiHandle> kInner = ObjectsOf(vpiStmt, BodyOf(3));
  ASSERT_EQ(kInner.size(), 1U);
  ExpectGuarded(kInner[0], vpiAssignment);
}

TEST_F(DelayControlsEverywhere, ADelayInsideAForeverDelaysItsAssignment) {
  vpiHandle loop = BodyOf(4);
  ASSERT_NE(loop, nullptr);
  const std::vector<vpiHandle> kInner =
      ObjectsOf(vpiStmt, vpi_handle(vpiStmt, loop));
  ASSERT_EQ(kInner.size(), 1U);
  ExpectGuarded(kInner[0], vpiAssignment);
}

TEST_F(DelayControlsEverywhere, ARepeatedDelayDelaysItsAssignment) {
  vpiHandle loop = BodyOf(5);
  ASSERT_NE(loop, nullptr);
  ExpectGuarded(vpi_handle(vpiStmt, loop), vpiAssignment);
}

TEST_F(DelayControlsEverywhere, AMinTypMaxDelayIsAMinTypMaxOperation) {
  vpiHandle delay = DelayOf(6);
  ASSERT_NE(delay, nullptr);
  EXPECT_EQ(OpOf(delay), vpiMinTypMaxOp);
  std::vector<int> values;
  for (vpiHandle operand : OperandsOf(delay)) {
    values.push_back(IntegerOf(operand));
  }
  EXPECT_EQ(values, (std::vector<int>{1, 2, 3}));
}

TEST_F(DelayControlsEverywhere, AParameterDelayIsTheParameter) {
  vpiHandle delay = DelayOf(7);
  ASSERT_NE(delay, nullptr);
  EXPECT_EQ(vpi_get(vpiType, delay), vpiParameter);
  EXPECT_EQ(VpiObjectOf(delay), VpiObjectOf(By("top.P")));
}

TEST_F(DelayControlsEverywhere, APackageParameterDelayIsThatParameter) {
  vpiHandle delay = DelayOf(8);
  ASSERT_NE(delay, nullptr);
  EXPECT_EQ(vpi_get(vpiType, delay), vpiParameter);
  EXPECT_EQ(VpiObjectOf(delay), VpiObjectOf(By("pkg::D")));
}

TEST_F(DelayControlsEverywhere, ATimeLiteralDelayIsATimeConstant) {
  vpiHandle delay = DelayOf(9);
  ASSERT_NE(delay, nullptr);
  EXPECT_EQ(vpi_get(vpiType, delay), vpiConstant);
  EXPECT_EQ(vpi_get(vpiConstType, delay), vpiTimeConst);
}

TEST_F(DelayControlsEverywhere, ARealDelayIsARealConstant) {
  vpiHandle delay = DelayOf(10);
  ASSERT_NE(delay, nullptr);
  EXPECT_EQ(vpi_get(vpiType, delay), vpiConstant);
  EXPECT_EQ(vpi_get(vpiConstType, delay), vpiRealConst);
  s_vpi_value value = {};
  value.format = vpiRealVal;
  vpi_get_value(delay, &value);
  EXPECT_DOUBLE_EQ(value.value.real, 1.5);
}

TEST_F(DelayControlsEverywhere, AZeroDelayIsTheConstantZero) {
  vpiHandle delay = DelayOf(11);
  ASSERT_NE(delay, nullptr);
  EXPECT_EQ(vpi_get(vpiType, delay), vpiConstant);
  EXPECT_EQ(IntegerOf(delay), 0);
}

TEST_F(DelayControlsEverywhere, ATimeLiteralIsGivenAsItsOwnTime) {
  EXPECT_EQ(SimDelayOf(BodyOf(9)), 5000U);
}

TEST_F(DelayControlsEverywhere, ARealDelayIsGivenUntruncated) {
  EXPECT_EQ(SimDelayOf(BodyOf(10)), 15000U);
}

TEST_F(DelayControlsEverywhere, ANamedDelayIsGivenAsTheVariablesValue) {
  EXPECT_EQ(SimDelayOf(BodyOf(12)), 20000U);
}

TEST_F(DelayControlsEverywhere, AnIntraAssignmentDelayIsGivenThroughGetDelays) {
  EXPECT_EQ(SimDelayOf(IntraControlOf(13)), 50000U);
}

TEST_F(DelayControlsEverywhere, ANonblockingIntraAssignmentDelayHasNoStmt) {
  vpiHandle control = IntraControlOf(14);
  ASSERT_NE(control, nullptr);
  EXPECT_EQ(vpi_get(vpiType, control), vpiDelayControl);
  EXPECT_EQ(vpi_handle(vpiStmt, control), nullptr);
}

TEST_F(DelayControlsEverywhere, ANamedIntraAssignmentDelayHasNoStmt) {
  vpiHandle control = IntraControlOf(15);
  ASSERT_NE(control, nullptr);
  EXPECT_EQ(vpi_handle(vpiStmt, control), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiDelay, control)),
            VpiObjectOf(By("top.d")));
}

TEST_F(DelayControlsEverywhere, AMinTypMaxIntraAssignmentDelayHasNoStmt) {
  vpiHandle control = IntraControlOf(16);
  ASSERT_NE(control, nullptr);
  EXPECT_EQ(vpi_handle(vpiStmt, control), nullptr);
  EXPECT_EQ(OpOf(vpi_handle(vpiDelay, control)), vpiMinTypMaxOp);
}

class DelayControlsInEachPlace : public VpiDesignRun {
 protected:
  static vpiHandle FirstOf(vpiHandle stmt) {
    if (stmt == nullptr) return nullptr;
    if (vpi_get(vpiType, stmt) == vpiBegin) {
      const std::vector<vpiHandle> kInner = ObjectsOf(vpiStmt, stmt);
      return kInner.empty() ? nullptr : kInner[0];
    }
    return stmt;
  }

  static vpiHandle OwnedBy(vpiHandle owner) {
    return owner == nullptr ? nullptr : FirstOf(vpi_handle(vpiStmt, owner));
  }

  static vpiHandle OnlyProcessOf(vpiHandle scope) {
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, scope);
    return kProcs.size() == 1 ? OwnedBy(kProcs[0]) : nullptr;
  }
};

TEST_F(DelayControlsInEachPlace, ADelayControlInEachPlaceDelaysItsStmt) {
  Run("package pk; int v; task pt; #1 v = 1; endtask endpackage\n"
      "interface ifc; int v; initial #1 v = 1; endinterface\n"
      "program prg; int v; initial #1 v = 1; endprogram\n"
      "module top; int v; ifc i0(); prg p0();\n"
      "  class C; int m; task ct; #1 m = 1; endtask endclass\n"
      "  task tk; #1 v = 1; endtask\n"
      "  if (1) begin : g int w; initial #1 w = 1; end\n"
      "endmodule\n");
  vpiHandle top = By("top");
  const struct {
    const char* where;
    vpiHandle stmt;
  } kPlaces[] = {
      {"pt", OwnedBy(Named(vpiTask, By("pk"), "pt"))},
      {"i0", OnlyProcessOf(By("top.i0"))},
      {"p0", OnlyProcessOf(By("top.p0"))},
      {"ct", OwnedBy(Named(vpiMethods, Named(vpiClassDefn, top, "C"), "ct"))},
      {"tk", OwnedBy(Named(vpiTask, top, "tk"))},
      {"g", OnlyProcessOf(By("top.g"))},
  };
  for (const auto& place : kPlaces) {
    ASSERT_NE(place.stmt, nullptr) << place.where;
    EXPECT_EQ(vpi_get(vpiType, place.stmt), vpiDelayControl) << place.where;
    vpiHandle guarded = vpi_handle(vpiStmt, place.stmt);
    ASSERT_NE(guarded, nullptr) << place.where;
    EXPECT_EQ(vpi_get(vpiType, guarded), vpiAssignment) << place.where;
  }
}

TEST_F(DelayControlsInEachPlace, AnIntraAssignmentDelayInARoutineHasNoStmt) {
  Run("module top; int v, w;\n"
      "  class C; int m, n; task ct; m = #1 n; endtask endclass\n"
      "  task tk; v = #1 w; endtask\n"
      "endmodule\n");
  vpiHandle top = By("top");
  const struct {
    const char* where;
    vpiHandle stmt;
  } kPlaces[] = {
      {"ct", OwnedBy(Named(vpiMethods, Named(vpiClassDefn, top, "C"), "ct"))},
      {"tk", OwnedBy(Named(vpiTask, top, "tk"))},
  };
  for (const auto& place : kPlaces) {
    ASSERT_NE(place.stmt, nullptr) << place.where;
    EXPECT_EQ(vpi_get(vpiType, place.stmt), vpiAssignment) << place.where;
    vpiHandle control = vpi_handle(vpiDelayControl, place.stmt);
    ASSERT_NE(control, nullptr) << place.where;
    EXPECT_EQ(vpi_handle(vpiStmt, control), nullptr) << place.where;
    EXPECT_EQ(IntegerOf(vpi_handle(vpiDelay, control)), 1) << place.where;
  }
}

}  // namespace
}  // namespace delta
