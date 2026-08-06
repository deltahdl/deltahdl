// Tests for IEEE 1800-2023 clause 6.16.10 -- the string ASCII-to-real
// conversion method atoreal(). The subclause is a runtime leaf whose prototype
// returns a real value:
//   function real atoreal();
// The normative claims are:
//   * (C1) str.atoreal() returns the real number corresponding to the ASCII
//     decimal representation held in the string;
//   * (C2) the conversion scans a real constant (§5.7.2) and stops at the first
//     character that does not conform to that syntax, or at the end of string;
//   * (C3) the result is zero if no digit was encountered.
//
// The value the conversion reports depends entirely on how the source string is
// produced (a declaration initializer, a concatenation, a procedural
// reassignment, a cast from an integral value, or a parameter string constant
// -- all defined by clause 6.16, this pass's ancestor), and on the spelling of
// the real constant it scans (fraction, exponent, digit-separating underscore
// -- defined by §5.7.2, this pass's dependency). So every test builds the
// operand from real source syntax and drives it through the full pipeline
// (parse -> elaborate -> lower -> run), storing the real result into a real
// variable and reading its bit pattern back.

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// C1: the conversion returns the real value denoted by the string.
// ---------------------------------------------------------------------------

// §6.16.10 (C1): a fractional real constant in a declaration initializer.
TEST(StringMethods, AtorealFraction) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"3.14\";\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 3.14, 0.0001);
}

// §6.16.10 (C1): an integer-only spelling still yields the corresponding real.
TEST(StringMethods, AtorealIntegerString) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"42\";\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 42.0, 0.0001);
}

// ---------------------------------------------------------------------------
// C2: the scan conforms to real-constant syntax (§5.7.2) and stops at the
// first non-conforming character.
// ---------------------------------------------------------------------------

// §6.16.10 (C2) / §5.7.2: exponent (scientific) notation is a real constant.
// "1.5e2" -> 150.0.
TEST(StringMethods, AtorealExponentNotation) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"1.5e2\";\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 150.0, 0.0001);
}

// §6.16.10 (C2) / §5.7.2: a signed exponent is part of the real-constant
// syntax. "1e-3" -> 0.001.
TEST(StringMethods, AtorealNegativeExponent) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"1e-3\";\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 0.001, 0.000001);
}

// §6.16.10 (C2) / §5.7.2: an underscore between digits is a legal separator in
// a real constant, so it is scanned rather than terminating the conversion.
// "1_000.5" -> 1000.5.
TEST(StringMethods, AtorealScansDigitSeparatingUnderscore) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"1_000.5\";\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 1000.5, 0.0001);
}

// §6.16.10 (C2): the scan keeps the leading real constant and stops at the
// first character that does not conform. "2.5xyz" -> 2.5.
TEST(StringMethods, AtorealStopsAtNonConforming) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"2.5xyz\";\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 2.5, 0.0001);
}

// §6.16.10 (C2): a leading sign is accepted as part of the real value the
// string denotes. "-3.5" -> -3.5.
TEST(StringMethods, AtorealNegativeValue) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"-3.5\";\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, -3.5, 0.0001);
}

// ---------------------------------------------------------------------------
// C3: zero result when no digit is scanned.
// ---------------------------------------------------------------------------

// §6.16.10 (C3): a digit-free string yields zero.
TEST(StringMethods, AtorealNoDigitsReturnsZero) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(d, 0.0);
}

// §6.16.10 (C3): the empty string is the zero case. Source form: a declaration
// with no initializer, which clause 6.16 initializes to "".
TEST(StringMethods, AtorealEmptyStringReturnsZero) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s;\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(d, 0.0);
}

// §6.16.10 (C3, negative): a digit-free spelling that a naive C conversion
// would accept ("inf") is not a real constant, so with no digit scanned the
// result must be zero rather than infinity.
TEST(StringMethods, AtorealNonNumericKeywordReturnsZero) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"inf\";\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(d, 0.0);
}

// ---------------------------------------------------------------------------
// Input forms: the operand string produced by the various clause 6.16
// constructs (concatenation, reassignment, cast, parameter string), and the
// conversion result used as an expression operand.
// ---------------------------------------------------------------------------

// §6.16.10 (C1) with the concatenation operand form of clause 6.16: the three
// literals concatenate to "2.5", which atoreal reads as 2.5.
TEST(StringMethods, AtorealFromConcatenation) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s;\n"
      "  real r;\n"
      "  initial begin\n"
      "    s = {\"2\", \".\", \"5\"};\n"
      "    r = s.atoreal();\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 2.5, 0.0001);
}

// §6.16.10 (C1) with the procedural-reassignment operand form: atoreal reads
// the current value after the string has been reassigned to "6.25".
TEST(StringMethods, AtorealFromReassignment) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"0.0\";\n"
      "  real r;\n"
      "  initial begin\n"
      "    s = \"6.25\";\n"
      "    r = s.atoreal();\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 6.25, 0.0001);
}

// §6.16.10 (C1) with the cast operand form of clause 6.16: casting 16'h3334 to
// string yields the two ASCII bytes "34", which atoreal reads as 34.0.
TEST(StringMethods, AtorealFromCast) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s;\n"
      "  real r;\n"
      "  initial begin\n"
      "    s = string'(16'h3334);\n"
      "    r = s.atoreal();\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 34.0, 0.0001);
}

// §6.16.10 (C1) with the parameter-string operand form: a string constant
// (clause 6.16) supplies the operand. "7.5" -> 7.5.
TEST(StringMethods, AtorealFromParameterString) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  parameter string p = \"7.5\";\n"
      "  string s = p;\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 7.5, 0.0001);
}

// §6.16.10 (C1) in the expression-operand syntactic position: the real the
// conversion returns feeds an arithmetic expression rather than standing alone
// on the right-hand side. "2.5".atoreal() is 2.5, so 2.5 + 1.0 == 3.5.
TEST(StringMethods, AtorealResultAsExpressionOperand) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"2.5\";\n"
      "  real r;\n"
      "  initial r = s.atoreal() + 1.0;\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 3.5, 0.0001);
}

}  // namespace
