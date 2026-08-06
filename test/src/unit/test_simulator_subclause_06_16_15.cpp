// Tests for IEEE 1800-2023 clause 6.16.15 -- the string realtoa() built-in
// method. The subclause is a runtime leaf with a single normative sentence and
// a void prototype:
//   function void realtoa(real r);
// The claim is:
//   * str.realtoa(r) stores the ASCII real representation of r into str, which
//     is the inverse of the atoreal conversion (§6.16.10).
//
// realtoa is the real-valued analogue of the integer xtoa methods -- itoa
// (§6.16.11), hextoa (§6.16.12), octtoa (§6.16.13) and bintoa (§6.16.14) -- but
// takes a real argument instead of an integer, so it has its own evaluator
// (StringRealtoa). The text stored depends entirely on how the real argument is
// produced (a literal, a real variable, a parameter/localparam constant of
// 11.2.1, or an arithmetic expression) and on how the destination string is
// declared (clause 6.16, this pass's ancestor). realtoa is void, so there is no
// reject/error path; the "negative" case is the full-replacement behaviour --
// storing a shorter result must leave no residue of a longer prior value. Every
// test therefore builds both operands from real source syntax and drives them
// through the full pipeline (parse -> elaborate -> lower -> run). The void
// method mutates the string in place, so the stored value is observed with the
// == operator that clause 6.16 supplies (Table 6-9): the result string is
// compared against the expected spelling and that boolean is read out, or --
// for the explicit inverse-of-atoreal claim -- scanned back with atoreal
// (§6.16.10) and the real value read out.

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// The stored text is the ASCII real representation of the argument.
// ---------------------------------------------------------------------------

// §6.16.15: a fractional real literal is stored as its decimal spelling.
// Destination is a plain (empty-initialized) string of 6.16.
TEST(StringMethods, RealtoaStoresRealText) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.realtoa(2.5);\n"
      "    n = (s == \"2.5\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.15: zero is stored as the single character "0".
TEST(StringMethods, RealtoaZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.realtoa(0.0);\n"
      "    n = (s == \"0\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.15: a negative real value carries its sign into the stored spelling.
TEST(StringMethods, RealtoaNegativeValue) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.realtoa(-1.5);\n"
      "    n = (s == \"-1.5\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.15: an integer-valued real is spelled without a fractional part.
// 42.0 is stored as "42".
TEST(StringMethods, RealtoaIntegerValuedReal) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.realtoa(42.0);\n"
      "    n = (s == \"42\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.15 (full replacement over a prior value): storing a shorter result over
// a longer prior string replaces the whole string -- none of the old "old
// value" survives, so the result is exactly "1" (length 1).
TEST(StringMethods, RealtoaReplacesLongerExisting) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"old value\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.realtoa(1.0);\n"
      "    n = (s == \"1\") && (s.len() == 1);\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.15 (inverse of atoreal): the real text realtoa stores, scanned back
// with atoreal (§6.16.10), recovers the original real value. 2.5 is exactly
// representable at the default formatting precision, so the round trip is
// exact.
TEST(StringMethods, RealtoaIsInverseOfAtoreal) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s;\n"
      "  real r;\n"
      "  initial begin\n"
      "    s.realtoa(2.5);\n"
      "    r = s.atoreal();\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 2.5, 0.0001);
}

// ---------------------------------------------------------------------------
// Input forms for the real argument r.
// ---------------------------------------------------------------------------

// §6.16.15: the prototype's declared argument type is `real`; a real variable
// supplies the value read at runtime and stored as its decimal spelling.
TEST(StringMethods, RealtoaFromRealVariable) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  real x = 3.5;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.realtoa(x);\n"
      "    n = (s == \"3.5\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// Note: the parameter/localparam constant forms of 11.2.1 are also valid input
// forms for r, but `real` parameter evaluation currently reads back as 0
// independent of realtoa (a plain `real r = P;` already yields 0). That defect
// belongs to the parameter machinery, not to §6.16.15's rule, so it is not
// exercised here; the real-variable and expression forms above cover a
// non-literal runtime value for r.

// §6.16.15: the argument may be an arithmetic expression; realtoa stores the
// spelling of the evaluated result. 1.5 + 1.0 -> 2.5 -> "2.5".
TEST(StringMethods, RealtoaFromExpressionArgument) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  real x = 1.5;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.realtoa(x + 1.0);\n"
      "    n = (s == \"2.5\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// ---------------------------------------------------------------------------
// The stored string is a normal string value usable by downstream 6.16
// machinery.
// ---------------------------------------------------------------------------

// §6.16.15: the string realtoa produced feeds a later concatenation
// (clause 6.16), confirming the stored value is an ordinary string operand.
// "2.5" concatenated with "V" is "2.5V".
TEST(StringMethods, RealtoaResultUsedInConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.realtoa(2.5);\n"
      "    u = {s, \"V\"};\n"
      "    n = (u == \"2.5V\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

}  // namespace
