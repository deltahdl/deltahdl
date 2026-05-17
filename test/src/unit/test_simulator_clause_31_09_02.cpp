#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

#include <gtest/gtest.h>

using namespace delta;

namespace {

TEST(NegativeTimingConditionRoles, TimestampBothNonNegativeIsBoth) {
  EXPECT_EQ(TimestampConditionRole( 5, 10),
            NegativeTimingConditionRole::kBoth);
}

TEST(NegativeTimingConditionRoles, TimecheckBothNonNegativeIsBoth) {
  EXPECT_EQ(TimecheckConditionRole( 5, 10),
            NegativeTimingConditionRole::kBoth);
}

TEST(NegativeTimingConditionRoles, BothZeroIsBoth) {
  EXPECT_EQ(TimestampConditionRole(0, 0), NegativeTimingConditionRole::kBoth);
  EXPECT_EQ(TimecheckConditionRole(0, 0), NegativeTimingConditionRole::kBoth);
}

TEST(NegativeTimingConditionRoles, NegativeSetupTimestampIsRef) {
  EXPECT_EQ(TimestampConditionRole( -10, 20),
            NegativeTimingConditionRole::kRef);
}

TEST(NegativeTimingConditionRoles, NegativeSetupTimecheckIsData) {
  EXPECT_EQ(TimecheckConditionRole( -10, 20),
            NegativeTimingConditionRole::kData);
}

TEST(NegativeTimingConditionRoles, NegativeHoldTimestampIsData) {
  EXPECT_EQ(TimestampConditionRole( 20, -10),
            NegativeTimingConditionRole::kData);
}

TEST(NegativeTimingConditionRoles, NegativeHoldTimecheckIsRef) {
  EXPECT_EQ(TimecheckConditionRole( 20, -10),
            NegativeTimingConditionRole::kRef);
}

TEST(NegativeTimingConditionRoles, BothNegativeIsNone) {
  EXPECT_EQ(TimestampConditionRole(-1, -1), NegativeTimingConditionRole::kNone);
  EXPECT_EQ(TimecheckConditionRole(-1, -1), NegativeTimingConditionRole::kNone);
}

TEST(NegativeTimingConditionRoles, NegativeSetupZeroHoldMatchesNegativeSetup) {
  EXPECT_EQ(TimestampConditionRole( -5, 0),
            NegativeTimingConditionRole::kRef);
  EXPECT_EQ(TimecheckConditionRole( -5, 0),
            NegativeTimingConditionRole::kData);
}

TEST(NegativeTimingConditionRoles, ZeroSetupNegativeHoldMatchesNegativeHold) {
  EXPECT_EQ(TimestampConditionRole( 0, -5),
            NegativeTimingConditionRole::kData);
  EXPECT_EQ(TimecheckConditionRole( 0, -5),
            NegativeTimingConditionRole::kRef);
}

TEST(NegativeTimingConditions, SetupholdBothConditionsSimulate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5, ntfr, 1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "  initial x = 8'd55;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST(NegativeTimingConditions, RecremBothConditionsSimulate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $recrem(posedge clk, rst, 8, 3, ntfr, 1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "  initial x = 8'd77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

}
