#include <gtest/gtest.h>

#include "fixture_elaborator.h"

// §28.11 defines a strength specification as two components: a strength0
// keyword (supply0/strong0/pull0/weak0/highz0) and a strength1 keyword
// (supply1/strong1/pull1/weak1/highz1), and states that the pairing
// (highz0, highz1) — in either written order — shall be illegal. The strength
// levels of Table 28-7 are exercised as a pure value mapping in
// test_simulator_clause_28_11; here we drive real source through the full
// pipeline and observe the elaborator applying the two-component / illegal-pair
// rules on an actual strength specification.

namespace {

// §28.11 component lists: one keyword drawn from each of the strength0 and
// strength1 sets forms a legal specification and elaborates cleanly.
TEST(LogicStrengthModeling, ValidStrength0Strength1PairElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (weak0, pull1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §28.11: the (highz0, highz1) pairing is illegal.
TEST(LogicStrengthModeling, Highz0Highz1PairIsIllegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (highz0, highz1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §28.11: the reverse ordering (highz1, highz0) is equally illegal.
TEST(LogicStrengthModeling, Highz1Highz0PairIsIllegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (highz1, highz0) g1(y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §28.11: only the both-highz pairing is illegal — highz on a single component,
// paired with a driving strength on the other, is a legal way to make a driver
// emit z in place of that logic value. These discriminate the pair rule from a
// blanket ban on highz.
TEST(LogicStrengthModeling, Highz0WithDrivingStrength1IsLegal) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (highz0, strong1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LogicStrengthModeling, DrivingStrength0WithHighz1IsLegal) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (strong0, highz1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §28.11 governs strength specifications wherever they appear, not only on
// gate primitives. The same illegal pairing on a strength-bearing continuous
// assignment is likewise rejected, while a legal pairing there elaborates.
TEST(LogicStrengthModeling, Highz0Highz1OnContinuousAssignIsIllegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, y;\n"
      "  assign (highz0, highz1) y = a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(LogicStrengthModeling, DrivingPairOnContinuousAssignIsLegal) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, y;\n"
      "  assign (strong0, weak1) y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §28.11 governs strength specifications in the third syntactic position too:
// the drive strength on a net declaration. The both-highz pair is rejected
// there as well.
TEST(LogicStrengthModeling, Highz0Highz1OnNetDeclarationIsIllegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a;\n"
      "  wire (highz0, highz1) w = a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(LogicStrengthModeling, DrivingPairOnNetDeclarationIsLegal) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a;\n"
      "  wire (pull0, highz1) w = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
