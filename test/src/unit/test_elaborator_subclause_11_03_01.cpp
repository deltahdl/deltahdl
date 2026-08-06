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
  // §6.7.1: a built-in net's data type shall be a 4-state integral type (or an
  // unpacked aggregate of such), so `wire real` is illegal independent of the
  // expression; a real-valued continuous-assignment target must be a variable
  // (§6.5/§10.3) or a user-defined nettype (§6.7.2). Using a real variable here
  // isolates the operator: the error must come from `&` applied to real
  // operands (§11.3.1), not from an illegal net declaration.
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  assign c = a & b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(RealOps, LegalOpOnRealInContAssign) {
  ElabFixture f;
  // §6.5/§10.3: a continuous assignment may drive a variable, and a real
  // variable is a valid target (§6.7.1 forbids a real built-in net). The `+`
  // operator is legal on real operands (§11.3.1), so this elaborates cleanly.
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  assign c = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, InsideOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = a inside {1.0, 2.0, 3.0};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, IncrementOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  initial begin a = 1.0; a++; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, DecrementOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  initial begin a = 1.0; a--; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, ImplicationOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic c;\n"
      "  initial c = a -> b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, EquivalenceOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic c;\n"
      "  initial c = a <-> b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, StructMemberRealAccessIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { real realval; } S;\n"
      "  S s;\n"
      "  real v;\n"
      "  initial v = s.realval;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, RealArrayElementAccessIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  initial begin i = 0; v = arr[i]; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §11.3.1 lists a union member alongside a structure member as a position where
// a real operand may appear. Reading a real member of an unpacked union into a
// real expression elaborates without error.
TEST(RealOps, UnionMemberRealAccessIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef union { real realval; longint bits; } U;\n"
      "  U u;\n"
      "  real v;\n"
      "  initial v = u.realval;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// The XNOR bitwise operator also spells as ^~, which is integral-only just like
// its ~^ form, so applying it to real operands must be rejected.
TEST(RealOps, BitwiseXnorCaretTildeOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  initial c = a ^~ b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// The ^~ spelling of the reduction XNOR operator is likewise integral-only and
// is not permitted on a real operand.
TEST(RealOps, ReductionXnorCaretTildeOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = ^~a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
