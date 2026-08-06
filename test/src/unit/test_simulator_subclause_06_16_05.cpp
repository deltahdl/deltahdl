// Tests for IEEE 1800-2023 clause 6.16.5 -- the string tolower() built-in
// method. The subclause is a runtime leaf with two normative claims about the
// result of str.tolower():
//   * it returns a new string whose characters are the lowercase form of the
//     characters in str;
//   * str itself is left unchanged.
// The prototype is "function string tolower()" -- no arguments, string result.
// It is the exact mirror of clause 6.16.4 (toupper), converting in the opposite
// direction.
//
// The characters tolower reports depend entirely on how the string operand is
// produced (a declaration initializer, a concatenation, a procedural
// reassignment, a cast from an integral value -- all defined by clause 6.16,
// this pass's dependency). So every behavioural test builds the operand from
// real source and drives it through the full pipeline (parse -> elaborate ->
// lower -> run). The string result is observed with the == operator that clause
// 6.16 supplies (Table 6-9): the tolower result is stored in a string variable
// and compared against the expected literal, and that boolean is read out.
// Claim two (str unchanged) is checked by comparing the original variable
// against its pre-call value after the method has run.

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §6.16.5: uppercase letters are converted to their lowercase form. Operand
// built from a plain declaration initializer (clause 6.16).
TEST(StringMethods, TolowerConvertsUppercaseToLowercase) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"HELLO\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.tolower();\n"
      "    n = (u == \"hello\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.5: a string already in lowercase is returned with the same characters
// -- the conversion is idempotent on letters that need no change.
TEST(StringMethods, TolowerLeavesLowercaseUnchanged) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"world\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.tolower();\n"
      "    n = (u == \"world\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.5: every uppercase letter in a mixed-case string is lowered while the
// already-lowercase letters stay put -- the whole string ends up lowercase.
TEST(StringMethods, TolowerConvertsMixedCase) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"HeLLo\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.tolower();\n"
      "    n = (u == \"hello\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.5: non-alphabetic characters (digits, punctuation, spaces) have no
// lowercase form and are carried through unchanged; only letters are affected.
TEST(StringMethods, TolowerPreservesNonAlphabetic) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"A1-B2 C!\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.tolower();\n"
      "    n = (u == \"a1-b2 c!\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.5: an empty string has no characters to convert, so tolower yields the
// empty string. Empty string supplied directly as the initializer.
TEST(StringMethods, TolowerOnEmptyStringYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.tolower();\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.5 + clause 6.16: a string declared without an initializer defaults to
// the empty string, so tolower on it also yields the empty string -- the rule
// reached through the default-initialization path.
TEST(StringMethods, TolowerOnDefaultInitializedYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.tolower();\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.5: tolower converts whatever the operand currently holds, including a
// string produced by concatenation (clause 6.16 operators) rather than a plain
// literal. {"FOO","BAR"} is "FOOBAR", which lowercases to "foobar".
TEST(StringMethods, TolowerOnConcatenatedOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = {\"FOO\", \"BAR\"};\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.tolower();\n"
      "    n = (u == \"foobar\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.5: the conversion reflects the string's current contents. Reassign the
// variable procedurally, then convert -- tolower follows the new value.
TEST(StringMethods, TolowerFollowsProceduralReassignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"AB\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s = \"XYZ\";\n"
      "    u = s.tolower();\n"
      "    n = (u == \"xyz\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.5: tolower converts a string produced by casting an integral value to
// string (clause 6.16). 16'h4869 casts to the two-character string "Hi", whose
// lowercase form is "hi" -- observed through the real cast production path.
TEST(StringMethods, TolowerOnCastFromIntegral) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] b = 16'h4869;\n"
      "  string s = string'(b);\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.tolower();\n"
      "    n = (u == \"hi\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.5 (second claim): str is unchanged by tolower. Convert, then compare
// the original variable against its pre-call value -- it must still read
// "HELLO" even though the returned string is "hello". Both facts are pinned in
// one boolean so the test fails if either the result is wrong or the source was
// mutated.
TEST(StringMethods, TolowerLeavesSourceUnchanged) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"HELLO\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.tolower();\n"
      "    n = (s == \"HELLO\") && (u == \"hello\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.5: the returned value is itself a string, usable wherever a string
// operand is expected. Feed the tolower result back into a concatenation
// (clause 6.16) and confirm the composed string -- exercises the result in a
// string-operand position rather than only on an assignment right-hand side.
TEST(StringMethods, TolowerResultUsableAsStringOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"GO\";\n"
      "  string u;\n"
      "  string w;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.tolower();\n"
      "    w = {u, \"!\"};\n"
      "    n = (w == \"go!\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

}  // namespace
