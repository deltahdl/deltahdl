#include <gtest/gtest.h>

#include <array>
#include <string>
#include <utility>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class AssignmentsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle OnlyAssignmentOf(const char* scope) {
    const std::vector<vpiHandle> kAssigns = ObjectsOf(vpiContAssign, By(scope));
    return kAssigns.size() == 1 ? kAssigns[0] : nullptr;
  }

  static vpiHandle AssignmentDriving(const char* scope, const char* target) {
    for (vpiHandle assign : ObjectsOf(vpiContAssign, By(scope))) {
      vpiHandle lhs = vpi_handle(vpiLhs, assign);
      if (lhs == nullptr) continue;
      const char* name = vpi_get_str(vpiName, lhs);
      if (name != nullptr && std::string(name) == target) return assign;
    }
    return nullptr;
  }

  static vpiHandle BitAtOffset(vpiHandle assign, int offset) {
    for (vpiHandle bit : ObjectsOf(vpiBit, assign)) {
      if (vpi_get(vpiOffset, bit) == offset) return bit;
    }
    return nullptr;
  }

  static std::string FullNameOf(vpiHandle obj) {
    const char* name = obj == nullptr ? nullptr : vpi_get_str(vpiFullName, obj);
    return name == nullptr ? "" : name;
  }

  static int ScalarOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiScalarVal;
    vpi_get_value(obj, &value);
    return value.value.scalar;
  }

  static std::vector<int> DelaysOf(vpiHandle obj) {
    std::array<s_vpi_time, 3> times = {};
    s_vpi_delay delay = {};
    delay.da = times.data();
    delay.no_of_delays = 3;
    delay.time_type = vpiSimTime;
    vpi_get_delays(obj, &delay);
    return {static_cast<int>(times[0].low), static_cast<int>(times[1].low),
            static_cast<int>(times[2].low)};
  }
};

constexpr const char* kAssignmentsInEveryScope =
    "module sub(input [1:0] c, output [1:0] d); assign d = ~c; endmodule\n"
    "module top; wire [1:0] x, z, y;\n"
    "  assign y = x;\n"
    "  sub u(.c(x), .d(z));\n"
    "  if (1) begin : g wire w; assign w = x[0]; end\n"
    "endmodule\n";

TEST_F(AssignmentsOfARun, AnAssignmentsModuleIsTheModuleAroundIt) {
  Run(kAssignmentsInEveryScope);
  EXPECT_EQ(FullNameOf(vpi_handle(vpiModule, OnlyAssignmentOf("top"))), "top");
  EXPECT_EQ(FullNameOf(vpi_handle(vpiModule, OnlyAssignmentOf("top.u"))),
            "top.u");
  EXPECT_EQ(FullNameOf(vpi_handle(vpiModule, OnlyAssignmentOf("top.g"))),
            "top");
}

TEST_F(AssignmentsOfARun, AnAssignmentBitsModuleIsItsAssignmentsModule) {
  Run(kAssignmentsInEveryScope);
  for (const char* scope : {"top", "top.u"}) {
    SCOPED_TRACE(scope);
    const std::vector<vpiHandle> kBits =
        ObjectsOf(vpiBit, OnlyAssignmentOf(scope));
    ASSERT_EQ(kBits.size(), 2U);
    for (vpiHandle bit : kBits) {
      EXPECT_EQ(FullNameOf(vpi_handle(vpiModule, bit)), scope);
    }
  }
}

TEST_F(AssignmentsOfARun, AnAssignmentWithoutADelayReachesNoDelay) {
  Run("module top; wire y, a; assign y = a; endmodule\n");
  vpiHandle assign = OnlyAssignmentOf("top");
  ASSERT_NE(assign, nullptr);
  EXPECT_EQ(vpi_handle(vpiDelay, assign), nullptr);
}

TEST_F(AssignmentsOfARun, DISABLED_AnAssignmentBitReachesItsAssignmentsDelay) {
  Run("module top; wire [3:0] v, w; assign #5 v = w; endmodule\n");
  vpiHandle assign = OnlyAssignmentOf("top");
  ASSERT_NE(assign, nullptr);
  vpiHandle bit = BitAtOffset(assign, 2);
  ASSERT_NE(bit, nullptr);
  vpiHandle delay = vpi_handle(vpiDelay, bit);
  ASSERT_NE(delay, nullptr);
  EXPECT_EQ(IntegerOf(delay), 5);
}

TEST_F(AssignmentsOfARun, DISABLED_AnAssignmentBitReachesBothSides) {
  Run("module top; wire [3:0] y, a, b; assign y = a & b; endmodule\n");
  vpiHandle assign = OnlyAssignmentOf("top");
  ASSERT_NE(assign, nullptr);
  const std::vector<vpiHandle> kBits = ObjectsOf(vpiBit, assign);
  ASSERT_EQ(kBits.size(), 4U);
  for (vpiHandle bit : kBits) {
    EXPECT_NE(vpi_handle(vpiLhs, bit), nullptr);
    EXPECT_NE(vpi_handle(vpiRhs, bit), nullptr);
  }
}

TEST_F(AssignmentsOfARun, AVariableTargetIsTheLeftSide) {
  Run("module top; logic v; wire a; assign v = a; endmodule\n");
  vpiHandle lhs = vpi_handle(vpiLhs, OnlyAssignmentOf("top"));
  ASSERT_NE(lhs, nullptr);
  EXPECT_EQ(FullNameOf(lhs), "top.v");
}

TEST_F(AssignmentsOfARun, AConcatenationTargetIsOneConcatenation) {
  Run("module top; wire p, q; wire [1:0] r; assign {p, q} = r; endmodule\n");
  vpiHandle lhs = vpi_handle(vpiLhs, OnlyAssignmentOf("top"));
  ASSERT_NE(lhs, nullptr);
  EXPECT_EQ(vpi_get(vpiType, lhs), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, lhs), vpiConcatOp);
  EXPECT_EQ(NamesOf(vpiOperand, lhs), (std::vector<std::string>{"p", "q"}));
}

TEST_F(AssignmentsOfARun, ABitSelectTargetIsTheSelectedBit) {
  Run("module top; wire [3:0] w; wire a; assign w[1] = a; endmodule\n");
  vpiHandle lhs = vpi_handle(vpiLhs, OnlyAssignmentOf("top"));
  ASSERT_NE(lhs, nullptr);
  const int kType = vpi_get(vpiType, lhs);
  EXPECT_TRUE(kType == vpiBitSelect || kType == vpiNetBit) << kType;
  EXPECT_EQ(IntegerOf(vpi_handle(vpiIndex, lhs)), 1);
}

TEST_F(AssignmentsOfARun, APartSelectTargetIsAPartSelect) {
  Run("module top; wire [3:0] w; wire [1:0] a; assign w[3:2] = a; endmodule\n");
  vpiHandle lhs = vpi_handle(vpiLhs, OnlyAssignmentOf("top"));
  ASSERT_NE(lhs, nullptr);
  EXPECT_EQ(vpi_get(vpiType, lhs), vpiPartSelect);
  EXPECT_EQ(IntegerOf(vpi_handle(vpiLeftRange, lhs)), 3);
  EXPECT_EQ(IntegerOf(vpi_handle(vpiRightRange, lhs)), 2);
}

TEST_F(AssignmentsOfARun, ANetDeclarationAssignmentsTargetIsTheDeclaredNet) {
  Run("module top; wire a; wire n = a; endmodule\n");
  vpiHandle lhs = vpi_handle(vpiLhs, OnlyAssignmentOf("top"));
  ASSERT_NE(lhs, nullptr);
  EXPECT_EQ(FullNameOf(lhs), "top.n");
}

TEST_F(AssignmentsOfARun, AnAscendingTargetsRightmostBitIsAtOffsetZero) {
  Run("module top; wire [0:3] y; assign y = 4'b0001; endmodule\n");
  vpiHandle assign = OnlyAssignmentOf("top");
  ASSERT_NE(assign, nullptr);
  EXPECT_EQ(ScalarOf(BitAtOffset(assign, 0)), vpi1);
  EXPECT_EQ(ScalarOf(BitAtOffset(assign, 3)), vpi0);
}

TEST_F(AssignmentsOfARun, OneDelayIsReadForRiseFallAndTurnOff) {
  Run("module top; wire y, a; assign #5 y = a; endmodule\n");
  EXPECT_EQ(DelaysOf(OnlyAssignmentOf("top")), (std::vector<int>{5, 5, 5}));
}

TEST_F(AssignmentsOfARun, ThreeDelaysAreReadAsWritten) {
  Run("module top; wire y, a; assign #(3, 4, 2) y = a; endmodule\n");
  EXPECT_EQ(DelaysOf(OnlyAssignmentOf("top")), (std::vector<int>{3, 4, 2}));
}

TEST_F(AssignmentsOfARun, DISABLED_AnAssignmentBitsDelaysAreItsAssignments) {
  Run("module top; wire [3:0] y, a; assign #(3, 4) y = a; endmodule\n");
  vpiHandle bit = BitAtOffset(OnlyAssignmentOf("top"), 1);
  ASSERT_NE(bit, nullptr);
  const std::vector<int> kDelays = DelaysOf(bit);
  const int kError = vpi_chk_error(nullptr);
  EXPECT_EQ(kError, 0);
  EXPECT_EQ(kDelays[0], 3);
  EXPECT_EQ(kDelays[1], 4);
}

TEST_F(AssignmentsOfARun,
       DISABLED_OnlyANetDeclarationAssignmentsBitsAreMarked) {
  Run("module top; wire [1:0] r, v; wire [1:0] w = r; assign v = r; "
      "endmodule\n");
  for (const auto& [target, marked] : {std::pair{"w", 1}, std::pair{"v", 0}}) {
    SCOPED_TRACE(target);
    const std::vector<vpiHandle> kBits =
        ObjectsOf(vpiBit, AssignmentDriving("top", target));
    ASSERT_EQ(kBits.size(), 2U);
    for (vpiHandle bit : kBits) {
      EXPECT_EQ(vpi_get(vpiNetDeclAssign, bit), marked);
    }
  }
}

struct WrittenStrength {
  const char* name;
  const char* items;
  int strength0;
  int strength1;
};

class EveryWrittenStrength
    : public AssignmentsOfARun,
      public ::testing::WithParamInterface<WrittenStrength> {};

TEST_P(EveryWrittenStrength, DISABLED_TheAssignmentReportsIt) {
  Run(std::string("module top; wire y, a;\n") + GetParam().items +
      "\nendmodule\n");
  vpiHandle assign = OnlyAssignmentOf("top");
  ASSERT_NE(assign, nullptr);
  EXPECT_EQ(vpi_get(vpiStrength0, assign), GetParam().strength0);
  EXPECT_EQ(vpi_get(vpiStrength1, assign), GetParam().strength1);
}

std::string WrittenStrengthName(
    const ::testing::TestParamInfo<WrittenStrength>& info) {
  return info.param.name;
}

INSTANTIATE_TEST_SUITE_P(
    OnAContinuousAssignment, EveryWrittenStrength,
    ::testing::Values(
        WrittenStrength{"ZeroThenOne", "  assign (pull0, strong1) y = a;",
                        vpiPullDrive, vpiStrongDrive},
        WrittenStrength{"OneThenZero", "  assign (strong1, pull0) y = a;",
                        vpiPullDrive, vpiStrongDrive},
        WrittenStrength{"OnANetDeclaration", "  wire (weak0, weak1) w = a;",
                        vpiWeakDrive, vpiWeakDrive},
        WrittenStrength{"NoneWritten", "  assign y = a;", vpiStrongDrive,
                        vpiStrongDrive}),
    WrittenStrengthName);

TEST_F(AssignmentsOfARun, DISABLED_AnAssignmentBitReportsTheDefaultStrengths) {
  Run("module top; wire [3:0] v, a; assign v = a; endmodule\n");
  const std::vector<vpiHandle> kBits =
      ObjectsOf(vpiBit, OnlyAssignmentOf("top"));
  ASSERT_EQ(kBits.size(), 4U);
  for (vpiHandle bit : kBits) {
    EXPECT_EQ(vpi_get(vpiStrength0, bit), vpiStrongDrive);
    EXPECT_EQ(vpi_get(vpiStrength1, bit), vpiStrongDrive);
  }
}

}  // namespace
}  // namespace delta
