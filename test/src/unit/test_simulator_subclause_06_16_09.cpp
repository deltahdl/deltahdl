// Tests for IEEE 1800-2023 clause 6.16.9 -- the string ASCII-to-integer
// conversion methods atoi(), atohex(), atooct(), and atobin(). The subclause is
// a runtime leaf whose prototypes all return an integer (32-bit) value:
//   function integer atoi();     // decimal interpretation
//   function integer atohex();   // hexadecimal interpretation
//   function integer atooct();   // octal interpretation
//   function integer atobin();   // binary interpretation
// The normative claims are:
//   * (C1) each method reads the string as an ASCII numeral in its radix and
//     returns the corresponding integer;
//   * (C2) the scan consumes the leading run of radix digits together with any
//     underscore characters and stops at the first other character or the end
//     of the string;
//   * (C3) the result is zero when no digit is scanned;
//   * (C4) the full integer-literal syntax (sign, size, apostrophe, base) is
//     NOT parsed -- such characters simply terminate the scan;
//   * (C5, NOTE) the result is a 32-bit value; a wider numeral truncates
//     silently.
//
// The value each method reports depends entirely on how the source string is
// produced (a declaration initializer, a concatenation, a procedural
// reassignment, a cast from an integral value, or a parameter string constant
// -- all defined by clause 6.16, this pass's dependency). So every test builds
// the operand from real source syntax and drives it through the full pipeline
// (parse -> elaborate -> lower -> run), storing the integer result in a
// variable and reading it out.

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// C1: basic conversion in each radix, from a plain declaration initializer.
// ---------------------------------------------------------------------------

// §6.16.9 (C1): atoi reads the decimal numeral. "42" -> 42.
TEST(StringMethods, AtoiDecimal) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"42\";\n"
      "  int n;\n"
      "  initial n = s.atoi();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 42u);
}

// §6.16.9 (C1): atohex reads the numeral as hexadecimal. "1f" -> 0x1f == 31.
TEST(StringMethods, AtohexLowercase) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"1f\";\n"
      "  int n;\n"
      "  initial n = s.atohex();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0x1fu);
}

// §6.16.9 (C1): atohex accepts the uppercase A-F digits as well as lowercase.
TEST(StringMethods, AtohexUppercaseDigits) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"1F\";\n"
      "  int n;\n"
      "  initial n = s.atohex();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0x1fu);
}

// §6.16.9 (C1): atooct reads the numeral as octal. "77" -> 077 == 63.
TEST(StringMethods, AtooctBasic) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"77\";\n"
      "  int n;\n"
      "  initial n = s.atooct();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 63u);
}

// §6.16.9 (C1): atobin reads the numeral as binary. "1010" -> 0b1010 == 10.
TEST(StringMethods, AtobinBasic) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"1010\";\n"
      "  int n;\n"
      "  initial n = s.atobin();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 10u);
}

// ---------------------------------------------------------------------------
// C2: the scan consumes the leading digit run and stops at the first other
// character, in each radix.
// ---------------------------------------------------------------------------

// §6.16.9 (C2): decimal scan keeps the leading digits and stops at the first
// non-digit. "123xyz" -> 123.
TEST(StringMethods, AtoiStopsAtNonDigit) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"123xyz\";\n"
      "  int n;\n"
      "  initial n = s.atoi();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 123u);
}

// §6.16.9 (C2): the hex scan stops at a character outside the hex digit set.
// "1fg2" -> 0x1f == 31 ('g' terminates the scan, so the trailing 2 is unseen).
TEST(StringMethods, AtohexStopsAtNonHexDigit) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"1fg2\";\n"
      "  int n;\n"
      "  initial n = s.atohex();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0x1fu);
}

// §6.16.9 (C2): the octal scan rejects a digit outside its radix. "78" -> 7
// (the 8 is not an octal digit and terminates the scan).
TEST(StringMethods, AtooctStopsAtNonOctalDigit) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"78\";\n"
      "  int n;\n"
      "  initial n = s.atooct();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 7u);
}

// §6.16.9 (C2): the binary scan rejects a digit outside its radix. "102" ->
// 0b10 == 2 (the 2 terminates the scan).
TEST(StringMethods, AtobinStopsAtNonBinaryDigit) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"102\";\n"
      "  int n;\n"
      "  initial n = s.atobin();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 2u);
}

// §6.16.9 (C2): underscore characters are scanned along with digits, so they
// neither terminate the conversion nor contribute to the value. "1_000" ->
// 1000.
TEST(StringMethods, AtoiScansUnderscores) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"1_000\";\n"
      "  int n;\n"
      "  initial n = s.atoi();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1000u);
}

// §6.16.9 (C2): underscore scanning applies in every radix, not just decimal.
// "1_010" as binary -> 0b1010 == 10.
TEST(StringMethods, AtobinScansUnderscores) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"1_010\";\n"
      "  int n;\n"
      "  initial n = s.atobin();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 10u);
}

// ---------------------------------------------------------------------------
// C3: zero result when no digit is scanned, in each radix.
// ---------------------------------------------------------------------------

// §6.16.9 (C3): decimal conversion of a digit-free string yields zero.
TEST(StringMethods, AtoiNoDigitsReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  int n;\n"
      "  initial n = s.atoi();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

// §6.16.9 (C3): hex conversion of a string with no hex digits yields zero.
TEST(StringMethods, AtohexNoDigitsReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"xyz\";\n"
      "  int n;\n"
      "  initial n = s.atohex();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

// §6.16.9 (C3): the empty string is the zero case as well. Source form: a
// declaration with no initializer, which clause 6.16 initializes to "".
TEST(StringMethods, AtoiEmptyStringReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial n = s.atoi();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

// ---------------------------------------------------------------------------
// C4: full integer-literal syntax is not parsed; such characters end the scan.
// ---------------------------------------------------------------------------

// §6.16.9 (C4): a leading sign is not recognized. "-5" begins with '-', which
// is not a digit, so the scan stops before any digit -> 0.
TEST(StringMethods, AtoiDoesNotParseSign) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"-5\";\n"
      "  int n;\n"
      "  initial n = s.atoi();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

// §6.16.9 (C4): size/apostrophe/base notation is not interpreted. "8'd2" keeps
// only the leading digit run "8" -- the apostrophe terminates the scan.
TEST(StringMethods, AtoiDoesNotParseSizedLiteral) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"8'd2\";\n"
      "  int n;\n"
      "  initial n = s.atoi();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 8u);
}

// §6.16.9 (C4): a "0x" base prefix is not interpreted by atohex. The scan reads
// the leading '0', then 'x' terminates it, so the trailing 1f is never reached
// -> 0.
TEST(StringMethods, AtohexDoesNotParseBasePrefix) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"0x1f\";\n"
      "  int n;\n"
      "  initial n = s.atohex();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

// ---------------------------------------------------------------------------
// Input forms: the operand string produced by the various clause 6.16
// constructs (concatenation, reassignment, cast, parameter string).
// ---------------------------------------------------------------------------

// §6.16.9 (C1) with the concatenation operand form of clause 6.16: the three
// literals concatenate to "123", which atoi reads as 123.
TEST(StringMethods, AtoiFromConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s = {\"1\", \"2\", \"3\"};\n"
      "    n = s.atoi();\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 123u);
}

// §6.16.9 (C1) with the procedural-reassignment operand form: atoi reads the
// current value of the string after it has been reassigned to "255".
TEST(StringMethods, AtoiFromReassignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"0\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s = \"255\";\n"
      "    n = s.atoi();\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 255u);
}

// §6.16.9 (C1) with the cast operand form of clause 6.16: casting 16'h3132 to
// string yields the two ASCII bytes "12", which atoi reads as 12.
TEST(StringMethods, AtoiFromCast) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s = string'(16'h3132);\n"
      "    n = s.atoi();\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 12u);
}

// §6.16.9 (C1) with the parameter-string operand form: a string constant
// (clause 6.16) supplies the operand that atohex converts. "ff" -> 255.
TEST(StringMethods, AtohexFromParameterString) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter string p = \"ff\";\n"
      "  string s = p;\n"
      "  int n;\n"
      "  initial n = s.atohex();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 255u);
}

// §6.16.9 (C1) with the string literal built from clause 5.9 escape sequences:
// the escapes "\x34\x35" produce the ASCII bytes '4' and '5', so the string is
// "45" and atoi reads 45. This drives the escape-sequence literal production
// path (clause 5.9 / clause 6.16) through the full pipeline.
TEST(StringMethods, AtoiFromEscapedLiteral) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\\x34\\x35\";\n"
      "  int n;\n"
      "  initial n = s.atoi();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 45u);
}

// §6.16.9 (C1) in the expression-operand syntactic position: the integer the
// conversion returns feeds an arithmetic expression rather than standing alone
// on the right-hand side. "23".atoi() is 23, so 23 + 100 == 123.
TEST(StringMethods, AtoiResultAsExpressionOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"23\";\n"
      "  int n;\n"
      "  initial n = s.atoi() + 100;\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 123u);
}

// ---------------------------------------------------------------------------
// C5 (NOTE): the result is a 32-bit value; a wider numeral truncates silently.
// ---------------------------------------------------------------------------

// §6.16.9 (C5): "1_0000_0001" as hexadecimal is 0x1_0000_0001, a 33-bit value.
// The conversion keeps only the low 32 bits, so the result is 1 -- truncation
// occurs with no error.
TEST(StringMethods, AtohexTruncatesToThirtyTwoBits) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"1_0000_0001\";\n"
      "  int n;\n"
      "  initial n = s.atohex();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

}  // namespace
