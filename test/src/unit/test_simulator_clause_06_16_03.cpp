// Tests for IEEE 1800-2023 clause 6.16.3 -- the string getc() built-in method.
// The subclause makes these normative claims about the runtime result of
// str.getc(i):
//   * it returns the ASCII code of the i-th character of str;
//   * if i < 0 or i >= str.len() it returns 0 (valid indices run 0..len-1);
//   * x = str.getc(j) is semantically equivalent to the indexed read x =
//   str[j].
// The code getc reports depends on how the string operand is produced (a
// declaration initializer, a concatenation, a procedural reassignment, a cast
// from an integral value -- all defined by clause 6.16, this pass's dependency)
// and on the index it is handed. So every behavioural test builds the operand
// from real source and drives it through the full pipeline (parse -> elaborate
// -> lower -> run), reading the value the method returns, rather than
// hand-constructing a string variable. The equivalence claim is observed with
// the indexed read that clause 6.16 already supplies, and the empty/length
// probes lean on len() (clause 6.16.1) -- both dependencies this pass may use.
//
// The prototype "function byte getc(int i)" (a byte result, i.e. exactly 8 bits
// wide) is a property of the method result itself, not of how the operand was
// produced, so it is pinned with a single-stage evaluation whose Logic4Vec
// width is directly observable.

#include "builders_ast.h"
#include "fixture_string.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §6.16.3: getc(i) returns the ASCII code of the i-th character. Interior index
// of a string built from a declaration initializer (clause 6.16); 'e' is 101.
TEST(StringMethods, GetcReturnsAsciiCodeOfCharacter) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int n;\n"
      "  initial n = s.getc(1);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, static_cast<uint64_t>('e'));
}

// §6.16.3: index 0 selects the leftmost (first) character -- the accepting edge
// of the valid 0..len-1 range. 'a' is 97.
TEST(StringMethods, GetcFirstCharacter) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  int n;\n"
      "  initial n = s.getc(0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, static_cast<uint64_t>('a'));
}

// §6.16.3: index len-1 selects the rightmost (last) character -- the other
// accepting edge. 'c' is 99.
TEST(StringMethods, GetcLastCharacter) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  int n;\n"
      "  initial n = s.getc(2);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, static_cast<uint64_t>('c'));
}

// §6.16.3: getc's index is a plain run-time argument, so it must accept a
// computed value supplied by an int variable, not only a literal.
TEST(StringMethods, GetcFromVariableIndex) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int i = 4;\n"
      "  int n;\n"
      "  initial n = s.getc(i);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, static_cast<uint64_t>('o'));
}

// §6.16.3 + clause 6.16.1: getc's index is an ordinary run-time int operand, so
// it can be produced by the len() method that this subclause's out-of-bounds
// rule itself references. len()-1 addresses the last valid character. Build the
// index from real len() source and drive the whole pipeline: for "hello" the
// last character is 'o'.
TEST(StringMethods, GetcIndexFromLenSelectsLastCharacter) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int n;\n"
      "  initial n = s.getc(s.len() - 1);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, static_cast<uint64_t>('o'));
}

// §6.16.3: getc reads whatever string the operand currently holds, including
// one produced by concatenation (clause 6.16 operators) rather than a plain
// literal. {"he","llo"} is "hello"; index 0 is 'h'.
TEST(StringMethods, GetcOnConcatenatedString) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = {\"he\", \"llo\"};\n"
      "  int n;\n"
      "  initial n = s.getc(0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, static_cast<uint64_t>('h'));
}

// §6.16.3: the code returned reflects the string's current contents. Re-assign
// the variable procedurally, then read -- getc follows the new value.
TEST(StringMethods, GetcFollowsProceduralReassignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"ab\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s = \"xyz\";\n"
      "    n = s.getc(1);\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, static_cast<uint64_t>('y'));
}

// §6.16.3: getc reads a string produced by casting an integral value to string
// (clause 6.16). 16'h4869 casts to the two-character string "Hi", so getc(0) is
// 'H' (72) -- observed through the real cast production path.
TEST(StringMethods, GetcOnCastFromIntegral) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] b = 16'h4869;\n"
      "  string s = string'(b);\n"
      "  int n;\n"
      "  initial n = s.getc(0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, static_cast<uint64_t>('H'));
}

// §6.16.3: the byte returned by getc is a usable integer operand, so it
// composes in a surrounding arithmetic expression rather than only standing
// alone on an assignment right-hand side. For "abc", getc(0)-getc(... ) etc.;
// here 'b'-'a' is 1. This exercises the method result in an expression-operand
// position.
TEST(StringMethods, GetcUsableAsOperandInExpression) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  int n;\n"
      "  initial n = s.getc(1) - s.getc(0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.3: an index equal to str.len() is out of bounds (valid indices run
// 0..len-1), so getc returns 0. Index 2 equals the length of "hi" -- the exact
// boundary that guards against an off-by-one in the production guard.
TEST(StringMethods, GetcIndexEqualToLengthReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hi\";\n"
      "  int n;\n"
      "  initial n = s.getc(2);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

// §6.16.3: a negative index (i < 0) is out of bounds and getc returns 0.
TEST(StringMethods, GetcNegativeIndexReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hi\";\n"
      "  int i = -1;\n"
      "  int n;\n"
      "  initial n = s.getc(i);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

// §6.16.3 + clause 6.16.1: an empty string has length 0, so every index is out
// of bounds and getc returns 0. Empty string supplied as the initializer.
TEST(StringMethods, GetcEmptyStringReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\";\n"
      "  int n;\n"
      "  initial n = s.getc(0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

// §6.16.3 + clause 6.16: a string with no initializer defaults to the empty
// string, so getc(0) on it also returns 0 -- the out-of-bounds rule reached
// through the default-initialization path.
TEST(StringMethods, GetcDefaultInitializedReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial n = s.getc(0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

// §6.16.3: x = str.getc(j) is semantically equivalent to the indexed read
// x = str[j]. Drive both forms on the same string at an in-range position and
// confirm getc yields the expected character code and matches the index read
// (clause 6.16 supplies the indexed read). For "world", index 2 is 'r' (114).
TEST(StringMethods, GetcEquivalentToIndexedRead) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"world\";\n"
      "  int n;\n"
      "  initial n = (s.getc(2) == \"r\") && (s.getc(2) == s[2]);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.3: the equivalence holds at the out-of-bounds boundary too -- getc(j)
// returns 0 for j >= len, and so does the indexed read str[j]. Both must be 0
// and must agree.
TEST(StringMethods, GetcEquivalentToIndexedReadOutOfBounds) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"world\";\n"
      "  int n;\n"
      "  initial n = (s.getc(5) == 0) && (s.getc(5) == s[5]);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.3 declares the prototype "function byte getc(int i)": the result is a
// byte, i.e. exactly 8 bits wide, independent of how the operand was produced.
// The width of the returned value is a property of the method result itself,
// observed directly on the evaluated vector.
TEST(StringMethods, GetcReturnsByteWidth) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(1)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);
}

}  // namespace
