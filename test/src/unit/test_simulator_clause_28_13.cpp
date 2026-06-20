

#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(StrengthReductionNonresistive, SupplyReducesToStrong) {
  EXPECT_EQ(ReduceNonresistive(Strength::kSupply), Strength::kStrong);
}

TEST(StrengthReductionNonresistive, StrongPassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kStrong), Strength::kStrong);
}

TEST(StrengthReductionNonresistive, PullPassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kPull), Strength::kPull);
}

TEST(StrengthReductionNonresistive, LargePassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kLarge), Strength::kLarge);
}

TEST(StrengthReductionNonresistive, WeakPassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kWeak), Strength::kWeak);
}

TEST(StrengthReductionNonresistive, MediumPassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kMedium), Strength::kMedium);
}

TEST(StrengthReductionNonresistive, SmallPassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kSmall), Strength::kSmall);
}

TEST(StrengthReductionNonresistive, HighzPassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kHighz), Strength::kHighz);
}

// The cases above pin the reduction table in isolation. The simulations below
// drive a real switch so the rule is observed exactly as production applies it
// during elaboration + lowering: a nonresistive switch (nmos/pmos/cmos) carries
// the data input's strength to its output, and a supply-strength source is the
// single case that is knocked down — to strong.
TEST(StrengthReductionNonresistive, NmosForwardsNonSupplyStrengthUnchanged) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (pull1, pull0) d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kPull);
}

TEST(StrengthReductionNonresistive, NmosReducesSupplySourceToStrong) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (supply1, supply0) d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kStrong);
}

TEST(StrengthReductionNonresistive, PmosReducesSupplySourceToStrong) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (supply1, supply0) d = 1'b1;\n"
      "  assign c = 1'b0;\n"
      "  pmos p1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kStrong);
}

TEST(StrengthReductionNonresistive, CmosReducesSupplySourceToStrong) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign (supply1, supply0) d = 1'b1;\n"
      "  assign nc = 1'b1;\n"
      "  assign pc = 1'b0;\n"
      "  cmos g1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kStrong);
}

}  // namespace
