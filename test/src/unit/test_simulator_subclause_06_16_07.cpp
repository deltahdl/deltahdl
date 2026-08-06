// Tests for IEEE 1800-2023 clause 6.16.7 -- the string icompare() built-in
// method. The subclause is a runtime leaf with a single normative claim:
//   * str.icompare(s) compares str against s the way the ANSI C strcmp function
//     does, both with regard to lexical ordering and with regard to the return
//     value, EXCEPT that the comparison is case insensitive -- zero when the
//     strings are equal ignoring case, a negative value when str orders before
//     s, and a positive value when str orders after s.
// The prototype is "function int icompare(string s)" -- one string argument and
// an int (32-bit signed) result. icompare is the case-folding sibling of
// compare (clause 6.16.6); the distinguishing property here is that upper- and
// lowercase letters that differ only in case must be treated as equal and must
// order as though both had a single case.
//
// The ordering claim is about the sign of the returned int, so the ordering
// tests read the raw int result out and inspect its sign as a signed 32-bit
// value -- observing icompare()'s own return value directly. The equal cases
// additionally fold the result into a == expression to exercise the value as an
// operand.
//
// What icompare reports depends entirely on how the two string operands are
// produced (a declaration initializer, a concatenation, a procedural
// reassignment, a cast from an integral value, a string literal argument, a
// parameter string constant -- all defined by clause 6.16, this pass's
// dependency; and the "\0" escape stripping of clause 5.9). So every test
// builds the operands from real source and drives them through the full
// pipeline (parse -> elaborate -> lower -> run).

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// Interpret the read-out variable as a signed 32-bit int, the declared width of
// icompare()'s result.
static int32_t AsInt(uint64_t v) {
  return static_cast<int32_t>(v & 0xFFFFFFFFu);
}

// §6.16.7: strings that are identical (same case) compare to zero, exactly as
// strcmp. Operands built from plain declaration initializers (clause 6.16).
TEST(StringMethods, IcompareEqualSameCaseReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

// §6.16.7: the core case-insensitive claim -- strings equal except for letter
// case compare to zero. "Hello" and "hello" differ only in the first letter's
// case, so icompare must report equality where a case-sensitive compare would
// not.
TEST(StringMethods, IcompareEqualIgnoringCaseReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"Hello\";\n"
      "  string u = \"hello\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

// §6.16.7: mixed casing on both operands still compares equal when the
// case-folded letters match.
TEST(StringMethods, IcompareMixedCaseEqualReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"HeLLo\";\n"
      "  string u = \"hEllO\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

// §6.16.7: when str orders lexically before s (comparison case-folded),
// icompare returns a negative value. 'c' < 'd' in the third position.
TEST(StringMethods, IcompareLessThanReturnsNegative) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  string u = \"abd\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_LT(AsInt(v), 0);
}

// §6.16.7: when str orders lexically after s, icompare returns a positive value
// -- the mirror of the previous test.
TEST(StringMethods, IcompareGreaterThanReturnsPositive) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abd\";\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_GT(AsInt(v), 0);
}

// §6.16.7: case insensitivity must govern the ordering SIGN, not just equality.
// A case-sensitive strcmp orders 'B' (0x42) before 'a' (0x61) and returns a
// negative result; folding both to a single case makes "b" sort after "a", so
// icompare must return a positive value. This pins that production case-folds
// before comparing rather than comparing raw bytes.
TEST(StringMethods, IcompareCaseFoldedOrderingIsPositive) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"B\";\n"
      "  string u = \"a\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_GT(AsInt(v), 0);
}

// §6.16.7: the mirror discriminator -- "abc" vs "ABD" folds to "abc" vs "abd"
// and orders negative, whereas a case-sensitive compare of 'a' (0x61) against
// 'A' (0x41) would order positive. Confirms the case fold flips the direction.
TEST(StringMethods, IcompareCaseFoldedOrderingIsNegative) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  string u = \"ABD\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_LT(AsInt(v), 0);
}

// §6.16.7: two empty strings are equal, so icompare returns zero.
TEST(StringMethods, IcompareBothEmptyReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\";\n"
      "  string u = \"\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

// §6.16.7: the empty string orders before any non-empty string, as strcmp
// treats the shorter, prefix string as smaller.
TEST(StringMethods, IcompareEmptyOrdersBeforeNonEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\";\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_LT(AsInt(v), 0);
}

// §6.16.7: a proper prefix orders before the longer string that contains it,
// even case-folded and even though no character position differs -- strcmp
// keeps reading until one string runs out. "abc" < "ABCD" case-folded.
TEST(StringMethods, IcomparePrefixOrdersBeforeLonger) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  string u = \"ABCD\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_LT(AsInt(v), 0);
}

// §6.16.7: reverse direction -- the longer string orders after its prefix.
TEST(StringMethods, IcompareLongerOrdersAfterPrefix) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"ABCD\";\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_GT(AsInt(v), 0);
}

// §6.16.7: a string compared against itself is equal, so icompare returns zero
// -- the reflexive case. The result is folded into a == expression to exercise
// it as an operand.
TEST(StringMethods, IcompareWithSelfReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"Hello\";\n"
      "  int n;\n"
      "  initial n = (s.icompare(s) == 0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.7: the argument s may be given as a string literal, which clause 6.16
// implicitly converts to string for the comparison. Case-differing literal
// argument still yields zero.
TEST(StringMethods, IcompareAgainstStringLiteralArgument) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"ABC\";\n"
      "  int n;\n"
      "  initial n = (s.icompare(\"abc\") == 0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.7 + clause 6.16: icompare operates on whatever the operand currently
// holds, including a string produced by concatenation rather than a plain
// literal. {"AB","c"} is "ABc", equal case-folded to "abc".
TEST(StringMethods, IcompareOnConcatenatedOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = {\"AB\", \"c\"};\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

// §6.16.7: the comparison reflects the string's current contents. Reassign the
// operand procedurally, then compare -- the result follows the new value.
TEST(StringMethods, IcompareFollowsProceduralReassignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"aaa\";\n"
      "  string u = \"xyz\";\n"
      "  int r;\n"
      "  initial begin\n"
      "    s = \"XYZ\";\n"
      "    r = s.icompare(u);\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

// §6.16.7 + clause 6.16: an operand produced by casting an integral value to
// string is compared like any other string. 16'h4869 casts to "Hi", equal
// case-folded to "HI".
TEST(StringMethods, IcompareOnCastFromIntegral) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] b = 16'h4869;\n"
      "  string s = string'(b);\n"
      "  string u = \"HI\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

// §6.16.7 + clause 6.16: the operand may be a string variable initialized from
// a parameter string constant -- a different declaration path than a plain
// literal initializer. icompare still sees the string value the parameter
// carried, and case folding applies.
TEST(StringMethods, IcompareOperandFromParameterString) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter string p = \"ABC\";\n"
      "  string s = p;\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

// §6.16.7 + clause 6.16: the argument s may itself be a parameter string
// constant, exercising the argument syntactic position with a non-literal
// production. Case-differing parameter value yields zero.
TEST(StringMethods, IcompareArgumentIsParameterString) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter string p = \"ABC\";\n"
      "  string s = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.icompare(p);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

// §6.16.7 + clause 6.16: the argument may be produced by concatenation rather
// than named directly, covering the argument position with a computed operand.
// {"AB","c"} is "ABc", equal case-folded to "abc".
TEST(StringMethods, IcompareArgumentIsConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.icompare({\"AB\", \"c\"});\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

// §6.16.7 + clauses 5.9/6.16: the operand may come from a string literal that
// contains the "\0" escape sequence, which clause 6.16 removes during the
// conversion to a string variable. "HEL\0LO" becomes "HELLO", equal case-folded
// to "hello" -- the escape-bearing literal (clause 5.9) is driven through the
// real conversion path into icompare.
TEST(StringMethods, IcompareOnLiteralWithNullEscapeStripped) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"HEL\\0LO\";\n"
      "  string u = \"hello\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

}  // namespace
