// Tests for IEEE 1800-2023 clause 6.16.11 -- the string itoa() built-in method.
// The subclause is a runtime leaf with a single normative sentence and a void
// prototype:
//   function void itoa(integer i);
// The claims are:
//   * (C1) the prototype takes an integer argument and returns nothing (void);
//     the call is a statement, not an expression operand;
//   * (C2) str.itoa(i) stores the ASCII decimal representation of i into str,
//     which is the inverse of the atoi conversion (§6.16.9).
//
// The text stored depends entirely on how the integer argument is produced (a
// literal, a variable, a parameter/localparam constant of 11.2.1, or an
// arithmetic expression) and on how the destination string is declared (clause
// 6.16, this pass's ancestor). itoa is void, so there is no reject/error path;
// the "negative" case is the full-replacement behaviour -- storing a shorter
// result must leave no residue of a longer prior value. Every test therefore
// builds both operands from real source syntax and drives them through the full
// pipeline (parse -> elaborate -> lower -> run). The void method mutates the
// string in place, so the stored value is observed with the == operator that
// clause 6.16 supplies (Table 6-9): the result string is compared against the
// expected literal and that boolean is read out, or -- for the explicit
// inverse-of-atoi claim -- scanned back with atoi and the integer read out.

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// C1/C2: itoa stores the decimal ASCII text of its argument into the string.
// ---------------------------------------------------------------------------

// §6.16.11 (C2): a positive integer literal is stored as its decimal spelling.
// Destination is a plain (empty-initialized) string declaration of clause 6.16.
TEST(StringMethods, ItoaStoresDecimalText) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.itoa(123);\n"
      "    n = (s == \"123\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.11 (C2): zero is stored as the single character "0" rather than an
// empty string.
TEST(StringMethods, ItoaZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.itoa(0);\n"
      "    n = (s == \"0\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.11 (C2, full replacement): storing a shorter decimal result over a
// longer prior value replaces the whole string -- no trailing characters of the
// old "999999" survive, so the result is exactly "7" (length 1).
TEST(StringMethods, ItoaReplacesLongerExisting) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"999999\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.itoa(7);\n"
      "    n = (s == \"7\") && (s.len() == 1);\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.11 (C2, inverse of atoi): the decimal text itoa stores, scanned back
// with atoi (§6.16.9), recovers the original integer value.
TEST(StringMethods, ItoaIsInverseOfAtoi) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int r;\n"
      "  initial begin\n"
      "    s.itoa(2024);\n"
      "    r = s.atoi();\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 2024u);
}

// ---------------------------------------------------------------------------
// Input forms for the integer argument i.
// ---------------------------------------------------------------------------

// §6.16.11 (C1): the prototype's declared argument type is `integer`; a 4-state
// integer variable supplies the value read at runtime and stored as decimal.
TEST(StringMethods, ItoaFromIntegerType) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  integer x = 89;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.itoa(x);\n"
      "    n = (s == \"89\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.11 (C1) with the parameter constant form of 11.2.1: a parameter
// supplies the integer whose decimal spelling is stored.
TEST(StringMethods, ItoaFromParameter) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter int P = 42;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.itoa(P);\n"
      "    n = (s == \"42\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.11 (C1) with the localparam constant form of 11.2.1.
TEST(StringMethods, ItoaFromLocalparam) {
  auto v = RunAndGet(
      "module t;\n"
      "  localparam int L = 500;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.itoa(L);\n"
      "    n = (s == \"500\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// §6.16.11 (C1): the argument may be an arithmetic expression; itoa stores the
// decimal spelling of the evaluated result. 40 + 2 -> "42".
TEST(StringMethods, ItoaFromExpressionArgument) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int x = 40;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.itoa(x + 2);\n"
      "    n = (s == \"42\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

// ---------------------------------------------------------------------------
// The stored string is a normal string value usable by downstream clause 6.16
// machinery.
// ---------------------------------------------------------------------------

// §6.16.11 (C2): the string itoa produced feeds a later concatenation
// (clause 6.16), confirming the stored value is an ordinary string operand.
// "12" concatenated with "3" is "123".
TEST(StringMethods, ItoaResultUsedInConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  string t;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.itoa(12);\n"
      "    t = {s, \"3\"};\n"
      "    n = (t == \"123\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

}  // namespace
