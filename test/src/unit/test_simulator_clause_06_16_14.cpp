// Tests for IEEE 1800-2023 clause 6.16.14 -- the string bintoa() built-in
// method. The subclause is a runtime leaf with a single normative sentence and
// a void prototype:
//   function void bintoa(integer i);
// The claim is:
//   * str.bintoa(i) stores the ASCII binary representation of i into str, which
//     is the inverse of the atobin conversion (§6.16.9).
//
// bintoa is the base-2 mirror of itoa (§6.16.11, base 10), hextoa (§6.16.12,
// base 16), and octtoa (§6.16.13, base 8); all four share the StringXtoa
// evaluator. The text stored depends entirely on how the integer argument is
// produced (a literal, a variable, a parameter/localparam constant of 11.2.1,
// or an arithmetic expression) and on how the destination string is declared
// (clause 6.16, this pass's ancestor). bintoa is void, so there is no
// reject/error path; the "negative" case is the full-replacement behaviour --
// storing a shorter result must leave no residue of a longer prior value. Every
// test therefore builds both operands from real source syntax and drives them
// through the full pipeline (parse -> elaborate -> lower -> run). The void
// method mutates the string in place, so the stored value is observed with the
// == operator that clause 6.16 supplies (Table 6-9): the result string is
// compared against the expected binary literal and that boolean is read out, or
// -- for the explicit inverse-of-atobin claim -- scanned back with atobin and
// the integer read out.

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// bintoa stores the binary ASCII text of its argument into the string.
// ---------------------------------------------------------------------------

// §6.16.14: a positive integer literal is stored as its binary spelling.
// Decimal 10 is binary "1010". Destination is a plain (empty-initialized)
// string of 6.16.
TEST(StringMethods, BintoaStoresBinaryText) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.bintoa(10);\n"
      "    n = (s == \"1010\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.14: zero is stored as the single character "0" rather than an empty
// string.
TEST(StringMethods, BintoaZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.bintoa(0);\n"
      "    n = (s == \"0\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.14 (full replacement): storing a shorter binary result over a longer
// prior value replaces the whole string -- no trailing characters of the old
// "1111" survive, so the result is exactly "1" (length 1).
TEST(StringMethods, BintoaReplacesLongerExisting) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"1111\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.bintoa(1);\n"
      "    n = (s == \"1\") && (s.len() == 1);\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.14 (inverse of atobin): the binary text bintoa stores, scanned back
// with atobin (§6.16.9), recovers the original integer value.
// 13 -> "1101" -> 13.
TEST(StringMethods, BintoaIsInverseOfAtobin) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int r;\n"
      "  initial begin\n"
      "    s.bintoa(13);\n"
      "    r = s.atobin();\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 13u);
}

// ---------------------------------------------------------------------------
// Input forms for the integer argument i.
// ---------------------------------------------------------------------------

// §6.16.14: the prototype's declared argument type is `integer`; a 4-state
// integer variable supplies the value read at runtime and stored as binary.
// Decimal 6 is binary "110".
TEST(StringMethods, BintoaFromIntegerType) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  integer x = 6;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.bintoa(x);\n"
      "    n = (s == \"110\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.14 with the parameter constant form of 11.2.1: a parameter supplies the
// integer whose binary spelling is stored. Decimal 5 is binary "101".
TEST(StringMethods, BintoaFromParameter) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter int P = 5;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.bintoa(P);\n"
      "    n = (s == \"101\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.14 with the localparam constant form of 11.2.1. Binary literal 'b1011
// is decimal 11, stored back as "1011".
TEST(StringMethods, BintoaFromLocalparam) {
  auto v = RunAndGet(
      "module t;\n"
      "  localparam int L = 'b1011;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.bintoa(L);\n"
      "    n = (s == \"1011\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.14: the argument may be an arithmetic expression; bintoa stores the
// binary spelling of the evaluated result. 'b1010 + 'b0001 -> 'b1011 -> "1011".
TEST(StringMethods, BintoaFromExpressionArgument) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int x = 'b1010;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.bintoa(x + 'b0001);\n"
      "    n = (s == \"1011\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// ---------------------------------------------------------------------------
// The stored string is a normal string value usable by downstream 6.16
// machinery.
// ---------------------------------------------------------------------------

// §6.16.14: the string bintoa produced feeds a later concatenation
// (clause 6.16), confirming the stored value is an ordinary string operand.
// "11" concatenated with "0" is "110".
TEST(StringMethods, BintoaResultUsedInConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.bintoa('b11);\n"
      "    u = {s, \"0\"};\n"
      "    n = (u == \"110\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

}  // namespace
