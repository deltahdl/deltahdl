// Tests for IEEE 1800-2023 clause 6.16.12 -- the string hextoa() built-in
// method. The subclause is a runtime leaf with a single normative sentence and
// a void prototype:
//   function void hextoa(integer i);
// The claim is:
//   * str.hextoa(i) stores the ASCII hexadecimal representation of i into str,
//     which is the inverse of the atohex conversion (§6.16.9).
//
// hextoa is the base-16 mirror of itoa (§6.16.11); both share the StringXtoa
// evaluator. The text stored depends entirely on how the integer argument is
// produced (a literal, a variable, a parameter/localparam constant of 11.2.1,
// or an arithmetic expression) and on how the destination string is declared
// (clause 6.16, this pass's ancestor). hextoa is void, so there is no
// reject/error path; the "negative" case is the full-replacement behaviour --
// storing a shorter result must leave no residue of a longer prior value.
// Every test therefore builds both operands from real source syntax and drives
// them through the full pipeline (parse -> elaborate -> lower -> run). The void
// method mutates the string in place, so the stored value is observed with the
// == operator that clause 6.16 supplies (Table 6-9): the result string is
// compared against the expected hex literal and that boolean is read out, or --
// for the explicit inverse-of-atohex claim -- scanned back with atohex and the
// integer read out.

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// hextoa stores the hexadecimal ASCII text of its argument into the string.
// ---------------------------------------------------------------------------

// §6.16.12: a positive integer literal is stored as its lowercase hex spelling.
// Destination is a plain (empty-initialized) string declaration of clause 6.16.
TEST(StringMethods, HextoaStoresHexText) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.hextoa(255);\n"
      "    n = (s == \"ff\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.12: zero is stored as the single character "0" rather than an empty
// string.
TEST(StringMethods, HextoaZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.hextoa(0);\n"
      "    n = (s == \"0\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.12 (full replacement): storing a shorter hex result over a longer prior
// value replaces the whole string -- no trailing characters of the old
// "ffffff" survive, so the result is exactly "7" (length 1).
TEST(StringMethods, HextoaReplacesLongerExisting) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"ffffff\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.hextoa(7);\n"
      "    n = (s == \"7\") && (s.len() == 1);\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.12 (inverse of atohex): the hex text hextoa stores, scanned back with
// atohex (§6.16.9), recovers the original integer value.
TEST(StringMethods, HextoaIsInverseOfAtohex) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int r;\n"
      "  initial begin\n"
      "    s.hextoa('hABC);\n"
      "    r = s.atohex();\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0xABCu);
}

// ---------------------------------------------------------------------------
// Input forms for the integer argument i.
// ---------------------------------------------------------------------------

// §6.16.12: the prototype's declared argument type is `integer`; a 4-state
// integer variable supplies the value read at runtime and stored as hex.
TEST(StringMethods, HextoaFromIntegerType) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  integer x = 'hBEE;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.hextoa(x);\n"
      "    n = (s == \"bee\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.12 with the parameter constant form of 11.2.1: a parameter supplies the
// integer whose hex spelling is stored.
TEST(StringMethods, HextoaFromParameter) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter int P = 'hFF;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.hextoa(P);\n"
      "    n = (s == \"ff\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.12 with the localparam constant form of 11.2.1.
TEST(StringMethods, HextoaFromLocalparam) {
  auto v = RunAndGet(
      "module t;\n"
      "  localparam int L = 'h500;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.hextoa(L);\n"
      "    n = (s == \"500\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.12: the argument may be an arithmetic expression; hextoa stores the hex
// spelling of the evaluated result. 'hF0 + 'hF -> 'hFF -> "ff".
TEST(StringMethods, HextoaFromExpressionArgument) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int x = 'hF0;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.hextoa(x + 'hF);\n"
      "    n = (s == \"ff\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// ---------------------------------------------------------------------------
// The stored string is a normal string value usable by downstream clause 6.16
// machinery.
// ---------------------------------------------------------------------------

// §6.16.12: the string hextoa produced feeds a later concatenation
// (clause 6.16), confirming the stored value is an ordinary string operand.
// "1f" concatenated with "0" is "1f0".
TEST(StringMethods, HextoaResultUsedInConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.hextoa('h1f);\n"
      "    u = {s, \"0\"};\n"
      "    n = (u == \"1f0\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

}  // namespace
