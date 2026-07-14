// Tests for IEEE 1800-2023 clause 6.16.8 -- the string substr() built-in
// method. The subclause is a runtime leaf with two normative claims about the
// result of str.substr(i, j):
//   * it returns a NEW string formed by the characters of str in positions i
//     through j, inclusive of both endpoints;
//   * if i < 0, or j < i, or j >= str.len(), the result is "" (the empty
//     string).
// The prototype is "function string substr(int i, int j)" -- two int (32-bit
// signed) arguments and a string result.
//
// substr returns a string, so its result is observed through the == operator
// that clause 6.16 supplies (Table 6-9): the substring is stored in a string
// variable (or used directly as a string operand) and compared against the
// expected literal, and that boolean is read out. The characters substr reports
// depend entirely on how the source string is produced (a declaration
// initializer, a concatenation, a procedural reassignment, a cast from an
// integral value, a parameter string constant -- all defined by clause 6.16,
// this pass's dependency) and on how the index arguments are produced (integer
// literals, int variables, or constant parameters). The j >= str.len() boundary
// is exercised with the len() method of clause 6.16.1, this pass's other
// dependency. So every test builds its operands from real source and drives
// them through the full pipeline (parse -> elaborate -> lower -> run).

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §6.16.8 (claim A): substr returns the characters in positions i through j,
// inclusive. "hello world" positions 6..10 spell "world". Source from a plain
// declaration initializer (clause 6.16).
TEST(StringMethods, SubstrMiddleRange) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello world\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(6, 10);\n"
      "    n = (u == \"world\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.8 (claim A): when i equals j the substring is the single character at
// that position -- the endpoints are inclusive on both sides.
TEST(StringMethods, SubstrSingleCharacterWhenIEqualsJ) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(2, 2);\n"
      "    n = (u == \"l\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.8 (claim A): a substring anchored at position 0 covers the leading
// characters. Positions 0..1 of "hello" are "he".
TEST(StringMethods, SubstrPrefixFromZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(0, 1);\n"
      "    n = (u == \"he\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.8 (claim A): a substring ending at the last valid index covers the
// trailing characters. Positions 3..4 of "hello" are "lo". This also pins the
// largest in-range j (str.len()-1) as accepted, the boundary opposite the
// j >= len() rejection.
TEST(StringMethods, SubstrSuffixToLastIndex) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(3, 4);\n"
      "    n = (u == \"lo\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.8 (claim A) + clause 6.16.1: the whole string is recovered with
// substr(0, len()-1). The j argument is produced from the len() method of
// clause 6.16.1 -- exercising the index argument built from this pass's other
// dependency and the largest legal j in one shot.
TEST(StringMethods, SubstrEntireStringViaLen) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(0, s.len() - 1);\n"
      "    n = (u == \"hello\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.8 (claim A) + clause 6.16: substr operates on whatever the operand
// currently holds, including a string produced by concatenation rather than a
// plain literal. {"foo","bar"} is "foobar"; positions 1..4 are "ooba".
TEST(StringMethods, SubstrOnConcatenatedOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = {\"foo\", \"bar\"};\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(1, 4);\n"
      "    n = (u == \"ooba\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.8 (claim A): the substring reflects the string's current contents.
// Reassign the operand procedurally, then take the substring -- substr follows
// the new value.
TEST(StringMethods, SubstrFollowsProceduralReassignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"aaaa\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s = \"wxyz\";\n"
      "    u = s.substr(1, 2);\n"
      "    n = (u == \"xy\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.8 (claim A) + clause 6.16: the operand may be produced by casting an
// integral value to string. 16'h4869 casts to "Hi"; positions 0..1 are "Hi" --
// observed through the real cast production path.
TEST(StringMethods, SubstrOnCastFromIntegral) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] b = 16'h4869;\n"
      "  string s = string'(b);\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(0, 1);\n"
      "    n = (u == \"Hi\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.8 (claim A) + clause 6.16: the operand may be a string variable
// initialized from a parameter string constant, a different declaration path
// than a plain literal initializer. substr still sees the value the parameter
// carried. "cat" positions 1..2 are "at".
TEST(StringMethods, SubstrOperandFromParameterString) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter string p = \"cat\";\n"
      "  string s = p;\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(1, 2);\n"
      "    n = (u == \"at\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.8 (claim A): the returned value is itself a string, usable wherever a
// string operand is expected. The substring is stored and then used as the
// source of a further substr and a concatenation (clause 6.16), confirming the
// result is a genuine string. substr(6,10) of "hello world" is "world"; its
// own substr(0,2) is "wor", concatenated with "!" to "wor!".
TEST(StringMethods, SubstrResultUsableAsStringOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello world\";\n"
      "  string u;\n"
      "  string w;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(6, 10);\n"
      "    w = {u.substr(0, 2), \"!\"};\n"
      "    n = (w == \"wor!\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.8 (claim B): when i is negative the result is the empty string. A
// negative index is one of the three rejection conditions.
TEST(StringMethods, SubstrNegativeIYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(-1, 2);\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.8 (claim B): when j < i the range is empty and substr returns "".
TEST(StringMethods, SubstrJLessThanIYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(3, 1);\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.8 (claim B): a negative j is a special case of j < i (for a
// non-negative i) and likewise yields "". Distinct from the negative-i case:
// here the upper bound is what falls out of range.
TEST(StringMethods, SubstrNegativeJYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(2, -1);\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.8 (claim B): when j is past the last index (j >= str.len()) the result
// is "". "hello" has length 5, so index 10 is out of range.
TEST(StringMethods, SubstrJBeyondLengthYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(0, 10);\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.8 (claim B) + clause 6.16.1: the j >= str.len() boundary is exact --
// j equal to the length (one past the last valid index) is already out of
// range. The bound is built from len() so the test pins j == len() precisely
// regardless of the string's contents.
TEST(StringMethods, SubstrJEqualToLengthYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(0, s.len());\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.8 (claim B) + clause 6.16: on an empty string every index is out of
// range (len() is 0, so any j >= 0 satisfies j >= str.len()), and substr
// returns "". The empty operand is supplied directly as the initializer.
TEST(StringMethods, SubstrOnEmptyStringYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(0, 0);\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.8 (claim B) + clause 6.16: a string declared without an initializer
// defaults to the empty string, a different operand-production path than an
// explicit "" literal. substr on it also sees length 0, so every index is out
// of range and the result is "" -- the rule reached through the
// default-initialization dependency path.
TEST(StringMethods, SubstrOnDefaultInitializedOperandYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(0, 0);\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

}  // namespace
