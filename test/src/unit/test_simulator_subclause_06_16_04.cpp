// Tests for IEEE 1800-2023 clause 6.16.4 -- the string toupper() built-in
// method. The subclause is a runtime leaf with two normative claims about the
// result of str.toupper():
//   * it returns a new string whose characters are the uppercase form of the
//     characters in str;
//   * str itself is left unchanged.
// The prototype is "function string toupper()" -- no arguments, string result.
//
// The characters toupper reports depend entirely on how the string operand is
// produced (a declaration initializer, a concatenation, a procedural
// reassignment, a cast from an integral value -- all defined by clause 6.16,
// this pass's dependency). So every behavioural test builds the operand from
// real source and drives it through the full pipeline (parse -> elaborate ->
// lower -> run). The string result is observed with the == operator that clause
// 6.16 supplies (Table 6-9): the toupper result is stored in a string variable
// and compared against the expected literal, and that boolean is read out.
// Claim two (str unchanged) is checked by comparing the original variable
// against its pre-call value after the method has run.

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §6.16.4: lowercase letters are converted to their uppercase form. Operand
// built from a plain declaration initializer (clause 6.16).
TEST(StringMethods, ToupperConvertsLowercaseToUppercase) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.toupper();\n"
      "    n = (u == \"HELLO\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.4: a string already in uppercase is returned with the same characters
// -- the conversion is idempotent on letters that need no change.
TEST(StringMethods, ToupperLeavesUppercaseUnchanged) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"WORLD\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.toupper();\n"
      "    n = (u == \"WORLD\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.4: every lowercase letter in a mixed-case string is raised while the
// already-uppercase letters stay put -- the whole string ends up uppercase.
TEST(StringMethods, ToupperConvertsMixedCase) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"HeLLo\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.toupper();\n"
      "    n = (u == \"HELLO\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.4: non-alphabetic characters (digits, punctuation, spaces) have no
// uppercase form and are carried through unchanged; only letters are affected.
TEST(StringMethods, ToupperPreservesNonAlphabetic) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"a1-b2 c!\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.toupper();\n"
      "    n = (u == \"A1-B2 C!\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.4: an empty string has no characters to convert, so toupper yields the
// empty string. Empty string supplied directly as the initializer.
TEST(StringMethods, ToupperOnEmptyStringYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.toupper();\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.4 + clause 6.16: a string declared without an initializer defaults to
// the empty string, so toupper on it also yields the empty string -- the rule
// reached through the default-initialization path.
TEST(StringMethods, ToupperOnDefaultInitializedYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.toupper();\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.4: toupper converts whatever the operand currently holds, including a
// string produced by concatenation (clause 6.16 operators) rather than a plain
// literal. {"foo","bar"} is "foobar", which uppercases to "FOOBAR".
TEST(StringMethods, ToupperOnConcatenatedOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = {\"foo\", \"bar\"};\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.toupper();\n"
      "    n = (u == \"FOOBAR\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.4: the conversion reflects the string's current contents. Reassign the
// variable procedurally, then convert -- toupper follows the new value.
TEST(StringMethods, ToupperFollowsProceduralReassignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"ab\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s = \"xyz\";\n"
      "    u = s.toupper();\n"
      "    n = (u == \"XYZ\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.4: toupper converts a string produced by casting an integral value to
// string (clause 6.16). 16'h4869 casts to the two-character string "Hi", whose
// uppercase form is "HI" -- observed through the real cast production path.
TEST(StringMethods, ToupperOnCastFromIntegral) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] b = 16'h4869;\n"
      "  string s = string'(b);\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.toupper();\n"
      "    n = (u == \"HI\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.4 (second claim): str is unchanged by toupper. Convert, then compare
// the original variable against its pre-call value -- it must still read
// "hello" even though the returned string is "HELLO". Both facts are pinned in
// one boolean so the test fails if either the result is wrong or the source was
// mutated.
TEST(StringMethods, ToupperLeavesSourceUnchanged) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.toupper();\n"
      "    n = (s == \"hello\") && (u == \"HELLO\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.4: the returned value is itself a string, usable wherever a string
// operand is expected. Feed the toupper result back into a concatenation
// (clause 6.16) and confirm the composed string -- exercises the result in a
// string-operand position rather than only on an assignment right-hand side.
TEST(StringMethods, ToupperResultUsableAsStringOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"go\";\n"
      "  string u;\n"
      "  string w;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.toupper();\n"
      "    w = {u, \"!\"};\n"
      "    n = (w == \"GO!\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

}  // namespace
