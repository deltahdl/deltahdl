#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(RealOps, CaseEqualityOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a === b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, CaseInequalityOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a !== b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, WildcardEqualityOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a ==? b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, BitwiseAndOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  initial c = a & b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, BitwiseOrOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  initial c = a | b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, BitwiseXorOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  initial c = a ^ b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, BitwiseNegOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  real c;\n"
      "  initial c = ~a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, ShiftOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  real c;\n"
      "  initial c = a << 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, ModulusOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  initial c = a % b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, LogicalAndOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic c;\n"
      "  initial c = a && b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, RelationalOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic c;\n"
      "  initial c = a > b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, ArithOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b, c;\n"
      "  initial c = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, LogicalEqualityOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a == b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, LogicalNegOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = !a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, UnaryPlusMinusOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b, c;\n"
      "  initial begin\n"
      "    b = +a;\n"
      "    c = -a;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, WildcardInequalityOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a !=? b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, RightShiftOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  real c;\n"
      "  initial c = a >> 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, ArithLeftShiftOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  real c;\n"
      "  initial c = a <<< 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, ArithRightShiftOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  real c;\n"
      "  initial c = a >>> 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, BitwiseXnorOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  initial c = a ~^ b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, ReductionAndOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = &a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, ReductionOrOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = |a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, ReductionXorOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = ^a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, ReductionNandOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = ~&a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, ReductionNorOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = ~|a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, ReductionXnorOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = ~^a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, ShortrealSubjectToSameRestrictions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  shortreal a, b;\n"
      "  shortreal c;\n"
      "  initial c = a & b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, RealtimeSubjectToSameRestrictions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  realtime a, b;\n"
      "  realtime c;\n"
      "  initial c = a & b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, LogicalOrOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic c;\n"
      "  initial c = a || b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, ConditionalOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b, c;\n"
      "  logic sel;\n"
      "  initial c = sel ? a : b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, PowerOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b, c;\n"
      "  initial c = a ** b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, IllegalOpOnRealInContAssign) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  wire real c;\n"
      "  assign c = a & b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, LegalOpOnRealInContAssign) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  wire real c;\n"
      "  assign c = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
