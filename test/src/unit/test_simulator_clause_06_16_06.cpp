// Tests for IEEE 1800-2023 clause 6.16.6 -- the string compare() built-in
// method. The subclause is a runtime leaf with a single normative claim:
//   * str.compare(s) compares str against s the way the ANSI C strcmp function
//     does, both with regard to lexical ordering and with regard to the return
//     value -- zero when the strings are equal, a negative value when str
//     orders before s, and a positive value when str orders after s.
// The prototype is "function int compare(string s)" -- one string argument and
// an int (32-bit signed) result. The subclause also points at the relational
// string operators of Table 6-9, but those operators are clause 6.16's rule,
// not this one, so every test here invokes .compare() directly.
//
// The ordering claim is about the sign of the returned int, so the ordering
// tests read the raw int result out and inspect its sign as a signed 32-bit
// value -- observing compare()'s own return value directly rather than routing
// it through the relational operators (whose signedness handling is a separate
// clause's concern). The equal cases additionally fold the result into a ==
// expression to exercise the value as an operand.
//
// What compare reports depends entirely on how the two string operands are
// produced (a declaration initializer, a concatenation, a procedural
// reassignment, a cast from an integral value, a string literal argument -- all
// defined by clause 6.16, this pass's dependency). So every test builds the
// operands from real source and drives them through the full pipeline (parse ->
// elaborate -> lower -> run).

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// Interpret the read-out variable as a signed 32-bit int, the declared width of
// compare()'s result.
static int32_t AsInt(uint64_t v) {
  return static_cast<int32_t>(v & 0xFFFFFFFFu);
}

// §6.16.6: equal strings compare to zero, exactly as strcmp. Operands built
// from plain declaration initializers (clause 6.16). The raw int result is read
// out directly to pin the numeric return value.
TEST(StringMethods, CompareEqualReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

// §6.16.6: when str orders lexically before s, compare returns a negative
// value. 'c' < 'd' in the third position.
TEST(StringMethods, CompareLessThanReturnsNegative) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  string u = \"abd\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_LT(AsInt(v), 0);
}

// §6.16.6: when str orders lexically after s, compare returns a positive value
// -- the mirror of the previous test.
TEST(StringMethods, CompareGreaterThanReturnsPositive) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abd\";\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_GT(AsInt(v), 0);
}

// §6.16.6: two empty strings are equal, so compare returns zero.
TEST(StringMethods, CompareBothEmptyReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\";\n"
      "  string u = \"\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

// §6.16.6: the empty string orders before any non-empty string (strcmp treats
// the shorter, prefix string as smaller). Empty operand supplied directly.
TEST(StringMethods, CompareEmptyOrdersBeforeNonEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\";\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_LT(AsInt(v), 0);
}

// §6.16.6: a proper prefix orders before the longer string that contains it,
// even though no character position differs -- strcmp keeps reading until one
// string runs out. "abc" < "abcd".
TEST(StringMethods, ComparePrefixOrdersBeforeLonger) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  string u = \"abcd\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_LT(AsInt(v), 0);
}

// §6.16.6: reverse direction -- the longer string orders after its prefix.
TEST(StringMethods, CompareLongerOrdersAfterPrefix) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abcd\";\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_GT(AsInt(v), 0);
}

// §6.16.6: compare is case-sensitive, as strcmp is -- it orders by character
// code. 'A' (0x41) precedes 'a' (0x61), so "ABC".compare("abc") is negative.
// This is the property that distinguishes compare from the case-insensitive
// icompare (clause 6.16.7).
TEST(StringMethods, CompareIsCaseSensitive) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"ABC\";\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_LT(AsInt(v), 0);
}

// §6.16.6: a string compared against itself is equal, so compare returns zero
// -- the reflexive case. The result is folded into a == expression to exercise
// it as an operand.
TEST(StringMethods, CompareWithSelfReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int n;\n"
      "  initial n = (s.compare(s) == 0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.6: the argument s may be given as a string literal, which clause 6.16
// implicitly converts to string for the comparison. Equal literal argument
// yields zero.
TEST(StringMethods, CompareAgainstStringLiteralArgument) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  int n;\n"
      "  initial n = (s.compare(\"abc\") == 0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.6 + clause 6.16: compare operates on whatever the operand currently
// holds, including a string produced by concatenation rather than a plain
// literal. {"ab","c"} is "abc", equal to "abc".
TEST(StringMethods, CompareOnConcatenatedOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = {\"ab\", \"c\"};\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

// §6.16.6: the comparison reflects the string's current contents. Reassign the
// operand procedurally, then compare -- the result follows the new value.
TEST(StringMethods, CompareFollowsProceduralReassignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"aaa\";\n"
      "  string u = \"xyz\";\n"
      "  int r;\n"
      "  initial begin\n"
      "    s = \"xyz\";\n"
      "    r = s.compare(u);\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

// §6.16.6 + clause 6.16: an operand produced by casting an integral value to
// string is compared like any other string. 16'h4869 casts to "Hi", equal to
// the literal "Hi".
TEST(StringMethods, CompareOnCastFromIntegral) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] b = 16'h4869;\n"
      "  string s = string'(b);\n"
      "  string u = \"Hi\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

// §6.16.6 + clause 6.16: the operand may be a string variable initialized from
// a parameter string constant -- a different declaration path than a plain
// literal initializer. compare still sees the string value the parameter
// carried.
TEST(StringMethods, CompareOperandFromParameterString) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter string p = \"abc\";\n"
      "  string s = p;\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

// §6.16.6 + clause 6.16: the argument s may itself be a parameter string
// constant, exercising the argument syntactic position with a non-literal
// production. Equal parameter value yields zero.
TEST(StringMethods, CompareArgumentIsParameterString) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter string p = \"abc\";\n"
      "  string s = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.compare(p);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

// §6.16.6 + clause 6.16: the argument may be produced by concatenation rather
// than named directly, covering the argument position with a computed operand.
// {"ab","c"} is "abc", equal to str "abc".
TEST(StringMethods, CompareArgumentIsConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.compare({\"ab\", \"c\"});\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

// §6.16.6 + clauses 5.9/6.16: the operand may come from a string literal that
// contains the "\0" escape sequence, which clause 6.16 removes during the
// conversion to a string variable. "hello\0world" becomes "helloworld", so
// compare against "helloworld" is equal -- the escape-bearing literal (clause
// 5.9) is driven through the real conversion path into compare.
TEST(StringMethods, CompareOnLiteralWithNullEscapeStripped) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\\0world\";\n"
      "  string u = \"helloworld\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

}  // namespace
