

#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

// ===========================================================================
// §5.7.2 Real literal constants
// ===========================================================================

// ---------------------------------------------------------------------------
// 1. Fixed-point decimal notation
// ---------------------------------------------------------------------------
TEST(SimCh50702, RealFixedPointDecimal) {
  // §5.7.2: Fixed-point decimal notation.
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 1.2;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 1.2);
}

// ---------------------------------------------------------------------------
// 2. Small fixed-point value
// ---------------------------------------------------------------------------
TEST(SimCh50702, RealSmallFixedPoint) {
  // §5.7.2 valid form: "0.1"
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 0.1;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 0.1);
}

// ---------------------------------------------------------------------------
// 3. Large fixed-point value
// ---------------------------------------------------------------------------
TEST(SimCh50702, RealLargeFixedPoint) {
  // §5.7.2 valid form: "2394.26331"
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 2394.26331;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 2394.26331);
}

// ---------------------------------------------------------------------------
// 4. Scientific notation with uppercase E
// ---------------------------------------------------------------------------
TEST(SimCh50702, RealScientificUpperE) {
  // §5.7.2: Scientific notation with uppercase E.
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 1.2E12;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 1.2e12);
}

// ---------------------------------------------------------------------------
// 5. Scientific notation with lowercase e and negative exponent
// ---------------------------------------------------------------------------
TEST(SimCh50702, RealScientificLowerENeg) {
  // §5.7.2 valid form: "1.30e-2"
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 1.30e-2;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 1.30e-2);
}

// ---------------------------------------------------------------------------
// 6. Scientific notation with zero exponent
// ---------------------------------------------------------------------------
TEST(SimCh50702, RealScientificZeroExponent) {
  // §5.7.2 valid form: "0.1e-0"
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 0.1e-0;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 0.1);
}

// ---------------------------------------------------------------------------
// 7. Integer with scientific notation (no decimal point)
// ---------------------------------------------------------------------------
TEST(SimCh50702, RealIntegerScientific) {
  // §5.7.2 valid form: "23E10"
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 23E10;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 23e10);
}

// ---------------------------------------------------------------------------
// 8. Integer with negative exponent
// ---------------------------------------------------------------------------
TEST(SimCh50702, RealIntegerNegativeExponent) {
  // §5.7.2 valid form: "29E-2"
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 29E-2;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 29e-2);
}

// ---------------------------------------------------------------------------
// 9. Underscores are ignored in real literals
// ---------------------------------------------------------------------------
TEST(SimCh50702, RealUnderscoreIgnored) {
  // §5.7.2: Underscores in real literals are ignored.
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 236.123_763_e-12;\nendmodule\n",
      "x");
  EXPECT_DOUBLE_EQ(v, 236.123763e-12);
}

// ---------------------------------------------------------------------------
// 10. Negative real via unary minus
// ---------------------------------------------------------------------------
TEST(SimCh50702, RealNegativeUnaryMinus) {
  // Unary minus applied to a real literal (§5.7.2 + §11.3).
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = -1.5;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, -1.5);
}

// ---------------------------------------------------------------------------
// 11. Scientific notation with explicit positive exponent sign
// ---------------------------------------------------------------------------
TEST(SimCh50702, RealExponentPositiveSign) {
  // §5.7.2 syntax: exp [ sign ] unsigned_number — sign can be '+'
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 1.0e+2;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 100.0);
}

// ---------------------------------------------------------------------------
// 12. IEEE 754 double-precision bit-exact storage
// ---------------------------------------------------------------------------
TEST(SimCh50702, RealIEEE754BitExact) {
  // §5.7.2: IEEE 754 double-precision bit-exact storage.
  // Verify the 64-bit pattern matches IEEE 754 double for 1.0.
  auto bits =
      RunAndGet("module t;\n  real x;\n  initial x = 1.0;\nendmodule\n", "x");
  uint64_t expected = 0x3FF0000000000000ULL;  // IEEE 754: 1.0
  EXPECT_EQ(bits, expected);
}

// ---------------------------------------------------------------------------
// 13. Real literal in arithmetic expression
// ---------------------------------------------------------------------------
TEST(SimCh50702, RealArithmeticExpression) {
  // Verify real arithmetic works end-to-end with literals.
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 1.5 + 2.25;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 3.75);
}

// ---------------------------------------------------------------------------
// 14. Real literal assigned to real variable preserves value
// ---------------------------------------------------------------------------
TEST(SimCh50702, RealVariablePreservesValue) {
  // §5.7.2: Verify round-trip through variable assignment.
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 3.14159265358979;\nendmodule\n",
      "x");
  EXPECT_DOUBLE_EQ(v, 3.14159265358979);
}

// ---------------------------------------------------------------------------
// 15. Large scientific notation value
// ---------------------------------------------------------------------------
TEST(SimCh50702, RealLargeScientific) {
  // §5.7.2 valid form: "39e8" (mentioned in spec text)
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 39e8;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 39e8);
}
// § real_number — scientific notation simulates
TEST(SimA87, ScientificNotation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real x;\n"
      "  initial x = 1.5e3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_DOUBLE_EQ(ToDouble(var), 1500.0);
}

// § real_number — scientific with positive exponent
TEST(SimA87, ScientificPositiveExp) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real x;\n"
      "  initial x = 1.0e+2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_DOUBLE_EQ(ToDouble(var), 100.0);
}

// § real_number — scientific with negative exponent
TEST(SimA87, ScientificNegativeExp) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real x;\n"
      "  initial x = 1.0e-2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_DOUBLE_EQ(ToDouble(var), 0.01);
}

// § exp — uppercase E
TEST(SimA87, ExpUppercase) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real x;\n"
      "  initial x = 2.5E2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_DOUBLE_EQ(ToDouble(var), 250.0);
}
