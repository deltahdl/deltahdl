// Tests for IEEE 1800-2023 clause 6.16.2 -- the string putc() built-in method.
// The subclause makes these normative claims about the runtime effect of
// str.putc(i, c):
//   * it replaces the i-th character of str with the given integral value;
//   * it never changes the size of str -- if i < 0 or i >= str.len() the string
//     is left unchanged (valid indices run 0..len-1);
//   * if the value c is zero the string is unaffected;
//   * str.putc(j, x) is semantically equivalent to the indexed assignment
//     str[j] = x.
// putc mutates the string in place, and its effect depends on how the operand
// string was produced (a declaration initializer, a concatenation, a procedural
// reassignment -- all defined by clause 6.16, this pass's ancestor) and on the
// index/value it is handed. So every behavioural test builds the operand from
// real source and drives it through the full pipeline (parse -> elaborate ->
// lower -> run), then observes the outcome with constructs clause 6.16 already
// supplies -- string equality (==), len(), and indexed read/assign -- rather
// than hand-constructing a string variable. Only the len()-based length probe
// leans on the 6.16.1 dependency, which this pass may use freely.

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §6.16.2: putc replaces the i-th character. Leftmost position (index 0) of a
// string built from a declaration initializer (clause 6.16). Observe the whole
// resulting string via the == operator.
TEST(StringMethods, PutcReplacesFirstCharacter) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(0, \"H\");\n"
      "    n = (s == \"Hello\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.2: replacement at the last valid position, index N-1 (here 4 for a
// five-character string). This pins the accepting edge of the 0..len-1 range.
TEST(StringMethods, PutcReplacesLastCharacter) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(4, \"O\");\n"
      "    n = (s == \"hellO\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.2: replacement at an interior position, with the index supplied by an
// int variable rather than a literal -- putc's index is a plain run-time
// argument, so it must accept a computed value.
TEST(StringMethods, PutcReplacesMiddleCharacterFromVariableIndex) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int i = 1;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(i, \"a\");\n"
      "    n = (s == \"hallo\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.2: the replacement value is "the given integral value" -- it need not
// be a character-literal operand. Supply the ASCII code of 'A' as a plain
// numeric literal and confirm the character it produces.
TEST(StringMethods, PutcAcceptsNumericIntegralValue) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(0, 65);\n"  // 65 == "A"
      "    n = (s == \"Abc\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.2: the value may come from a byte variable, not only an inline literal.
TEST(StringMethods, PutcAcceptsByteVariableValue) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  byte c = \"Z\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(2, c);\n"
      "    n = (s == \"abZ\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.2: putc operates on whatever string the operand currently holds,
// including one produced by concatenation (clause 6.16 operators) rather than a
// plain literal.
TEST(StringMethods, PutcOperatesOnConcatenatedString) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = {\"he\", \"llo\"};\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(0, \"H\");\n"
      "    n = (s == \"Hello\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.2: putc does not change the size of str. After a valid in-bounds write
// the character count is unchanged -- observe with len() (clause 6.16.1).
TEST(StringMethods, PutcPreservesStringLength) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(0, \"H\");\n"
      "    n = s.len();\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 5u);
}

// §6.16.2: an index at or past str.len() is out of bounds (valid indices run
// 0..len-1), so putc leaves the string unchanged. Index 5 equals the length of
// "hello" -- the exact boundary that guards against an off-by-one.
TEST(StringMethods, PutcIndexEqualToLengthLeavesStringUnchanged) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(5, \"X\");\n"
      "    n = (s == \"hello\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.2: a negative index (i < 0) is out of bounds and putc is a no-op.
TEST(StringMethods, PutcNegativeIndexLeavesStringUnchanged) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int i = -1;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(i, \"X\");\n"
      "    n = (s == \"hello\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.2 + clause 6.16: an empty string has length 0, so every index is out of
// bounds and putc cannot grow it -- the string stays empty.
TEST(StringMethods, PutcOnEmptyStringLeavesItEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(0, \"X\");\n"
      "    n = (s == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.2: if the value c is zero the string is unaffected, even at an
// otherwise valid in-bounds index. This mirrors clause 6.16's rule that
// assigning 0 to a string character is ignored.
TEST(StringMethods, PutcZeroValueLeavesStringUnchanged) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(0, 0);\n"
      "    n = (s == \"abc\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.2: str.putc(j, x) is semantically equivalent to the indexed assignment
// str[j] = x. Drive both forms from identical source strings and confirm they
// produce equal results (clause 6.16 supplies both the indexed assign and ==).
TEST(StringMethods, PutcEquivalentToIndexedAssignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u = \"hello\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(1, \"a\");\n"
      "    u[1] = \"a\";\n"
      "    n = (s == u);\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

}  // namespace
