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

}  // namespace
