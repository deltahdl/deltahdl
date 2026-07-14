// Tests for IEEE 1800-2023 clause 6.16.1 -- the string len() built-in method.
// The subclause makes two normative claims about the runtime result:
//   * str.len() yields the number of characters currently in str.
//   * when str is the empty string "", str.len() yields 0.
// The count len() reports is produced by how the string operand is built: a
// declaration initializer, a procedural assignment, or a concatenation (clause
// 6.16, this pass's dependency, defines those forms and the empty-string
// default). So every value test builds the string from real source and drives
// it through the full pipeline (parse -> elaborate -> lower -> run), reading
// the int the method returns, rather than hand-constructing a string variable.
//
// The prototype "function int len();" (an int result independent of length) is
// a property of the method result itself, not of how the operand was produced,
// so it is pinned with a single-stage evaluation whose Logic4Vec width is
// directly observable.

#include "builders_ast.h"
#include "fixture_string.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §6.16.1: len() returns the number of characters in the string. Operand built
// from a string-literal declaration initializer (clause 6.16).
TEST(StringMethods, LenCountsCharactersOfLiteralInit) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int n;\n"
      "  initial n = s.len();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 5u);
}

// §6.16.1: len() counts characters, which is distinct from counting the bytes
// written in source. Clause 6.16 removes "\0" characters when a literal is
// assigned to a string, so a six-glyph literal containing one "\0" holds five
// characters and len() reports 5. This isolates "number of characters" from
// "number of source bytes".
TEST(StringMethods, LenCountsCharactersNotSourceBytes) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"ab\\0cd\";\n"
      "  int n;\n"
      "  initial n = s.len();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 4u);
}

// §6.16.1: len() reflects a string produced by concatenation (clause 6.16
// operators), not just a plain literal -- {"foo","bar"} is six characters.
TEST(StringMethods, LenOfConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = {\"foo\", \"bar\"};\n"
      "  int n;\n"
      "  initial n = s.len();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 6u);
}

// §6.16.1: the count is of the string's current contents. Re-assign the
// variable procedurally, then measure -- len() follows the new value.
TEST(StringMethods, LenFollowsProceduralReassignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"ab\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s = \"abcdef\";\n"
      "    n = s.len();\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 6u);
}

// §6.16.1: len() reports the character count of a string produced by casting an
// integral value to string (clause 6.16). 16'h4869 casts to the two-character
// string "Hi", so len() is 2 -- observed through the real cast production path,
// not a hand-built string.
TEST(StringMethods, LenOfCastFromIntegral) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] b = 16'h4869;\n"
      "  string s = string'(b);\n"
      "  int n;\n"
      "  initial n = s.len();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 2u);
}

// §6.16.1: the int returned by len() is a usable integer operand, so it
// composes in a surrounding arithmetic expression rather than only standing
// alone on an assignment right-hand side. For "hello", len()*2 - 1 is 9. This
// exercises the method result in an expression-operand position end-to-end.
TEST(StringMethods, LenUsableAsIntOperandInExpression) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int n;\n"
      "  initial n = s.len() * 2 - 1;\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 9u);
}

// §6.16.1: if str is "", len() returns 0. Empty string supplied explicitly as
// the declaration initializer.
TEST(StringMethods, LenEmptyLiteralIsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\";\n"
      "  int n;\n"
      "  initial n = s.len();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

// §6.16.1 + clause 6.16: a string with no initializer defaults to the empty
// string, so len() on it also returns 0. This is the boundary/negative form of
// the character-count rule reached through the default-initialization path.
TEST(StringMethods, LenDefaultInitializedIsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial n = s.len();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

// §6.16.1 declares the prototype "function int len();": the result is an int,
// i.e. a 32-bit value, independent of how long the string is. The width of the
// returned value is a property of the method result itself, observed directly
// on the evaluated vector.
TEST(StringMethods, LenReturnsIntWidth) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "len");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

}  // namespace
