// Tests for IEEE 1800-2023 clause 6.16.13 -- the string octtoa() built-in
// method. The subclause is a runtime leaf with a single normative sentence and
// a void prototype:
//   function void octtoa(integer i);
// The claim is:
//   * str.octtoa(i) stores the ASCII octal representation of i into str, which
//     is the inverse of the atooct conversion (§6.16.9).
//
// octtoa is the base-8 mirror of itoa (§6.16.11, base 10) and hextoa (§6.16.12,
// base 16); all three share the StringXtoa evaluator. The text stored depends
// entirely on how the integer argument is produced (a literal, a variable, a
// parameter/localparam constant of 11.2.1, or an arithmetic expression) and on
// how the destination string is declared (clause 6.16, this pass's ancestor).
// octtoa is void, so there is no reject/error path; the "negative" case is the
// full-replacement behaviour -- storing a shorter result must leave no residue
// of a longer prior value. Every test therefore builds both operands from real
// source syntax and drives them through the full pipeline (parse -> elaborate
// -> lower -> run). The void method mutates the string in place, so the stored
// value is observed with the == operator that clause 6.16 supplies (Table 6-9):
// the result string is compared against the expected octal literal and that
// boolean is read out, or -- for the explicit inverse-of-atooct claim --
// scanned back with atooct and the integer read out.

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// octtoa stores the octal ASCII text of its argument into the string.
// ---------------------------------------------------------------------------

// §6.16.13: a positive integer literal is stored as its octal spelling. Decimal
// 8 is octal "10". Destination is a plain (empty-initialized) string of 6.16.
TEST(StringMethods, OcttoaStoresOctalText) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.octtoa(8);\n"
      "    n = (s == \"10\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.13: zero is stored as the single character "0" rather than an empty
// string.
TEST(StringMethods, OcttoaZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.octtoa(0);\n"
      "    n = (s == \"0\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.13 (full replacement): storing a shorter octal result over a longer
// prior value replaces the whole string -- no trailing characters of the old
// "7777" survive, so the result is exactly "7" (length 1).
TEST(StringMethods, OcttoaReplacesLongerExisting) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"7777\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.octtoa(7);\n"
      "    n = (s == \"7\") && (s.len() == 1);\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.13 (inverse of atooct): the octal text octtoa stores, scanned back with
// atooct (§6.16.9), recovers the original integer value. 511 -> "777" -> 511.
TEST(StringMethods, OcttoaIsInverseOfAtooct) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int r;\n"
      "  initial begin\n"
      "    s.octtoa(511);\n"
      "    r = s.atooct();\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 511u);
}

// ---------------------------------------------------------------------------
// Input forms for the integer argument i.
// ---------------------------------------------------------------------------

// §6.16.13: the prototype's declared argument type is `integer`; a 4-state
// integer variable supplies the value read at runtime and stored as octal.
// Decimal 64 is octal "100".
TEST(StringMethods, OcttoaFromIntegerType) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  integer x = 64;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.octtoa(x);\n"
      "    n = (s == \"100\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.13 with the parameter constant form of 11.2.1: a parameter supplies the
// integer whose octal spelling is stored. Decimal 8 is octal "10".
TEST(StringMethods, OcttoaFromParameter) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter int P = 8;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.octtoa(P);\n"
      "    n = (s == \"10\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.13 with the localparam constant form of 11.2.1. Octal literal 'o777 is
// decimal 511, stored back as "777".
TEST(StringMethods, OcttoaFromLocalparam) {
  auto v = RunAndGet(
      "module t;\n"
      "  localparam int L = 'o777;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.octtoa(L);\n"
      "    n = (s == \"777\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.13: the argument may be an arithmetic expression; octtoa stores the
// octal spelling of the evaluated result. 'o70 + 'o10 -> 'o100 -> "100".
TEST(StringMethods, OcttoaFromExpressionArgument) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int x = 'o70;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.octtoa(x + 'o10);\n"
      "    n = (s == \"100\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// ---------------------------------------------------------------------------
// The stored string is a normal string value usable by downstream 6.16
// machinery.
// ---------------------------------------------------------------------------

// §6.16.13: the string octtoa produced feeds a later concatenation
// (clause 6.16), confirming the stored value is an ordinary string operand.
// "17" concatenated with "0" is "170".
TEST(StringMethods, OcttoaResultUsedInConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.octtoa('o17);\n"
      "    u = {s, \"0\"};\n"
      "    n = (u == \"170\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

}  // namespace
