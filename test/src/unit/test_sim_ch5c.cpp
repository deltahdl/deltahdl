#include <gtest/gtest.h>

#include <cstring>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

struct SimCh5cFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, SimCh5cFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

static uint64_t RunAndGet(const std::string& src, const char* var_name) {
  SimCh5cFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var) return 0;
  return var->value.ToUint64();
}

static double RunAndGetReal(const std::string& src, const char* var_name) {
  SimCh5cFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return 0.0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var) return 0.0;
  double d = 0.0;
  uint64_t bits = var->value.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  return d;
}

// ===========================================================================
// §5.7 Numbers — simulation-level tests
//
// LRM §5.7: "Constant numbers can be specified as integer constants
// (see 5.7.1) or real constants (see 5.7.2)."
// Syntax 5-2: number ::= integral_number | real_number
// ===========================================================================

// ---------------------------------------------------------------------------
// 1. number ::= integral_number | real_number — both forms coexist
// ---------------------------------------------------------------------------
TEST(SimCh5c, NumberBothFormsCoexist) {
  // §5.7: Both integer and real constants in the same module.
  SimCh5cFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] i;\n"
      "  real r;\n"
      "  initial begin\n"
      "    i = 42;\n"
      "    r = 3.14;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(design, nullptr);
  if (!design) return;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vi = f.ctx.FindVariable("i");
  auto* vr = f.ctx.FindVariable("r");
  EXPECT_NE(vi, nullptr);
  EXPECT_NE(vr, nullptr);
  if (!vi || !vr) return;
  EXPECT_EQ(vi->value.ToUint64(), 42u);
  double d = 0.0;
  uint64_t bits = vr->value.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  EXPECT_DOUBLE_EQ(d, 3.14);
}

// ---------------------------------------------------------------------------
// 2. number ::= integral_number — decimal_number (unsigned_number form)
// ---------------------------------------------------------------------------
TEST(SimCh5c, NumberIntegralDecimal) {
  // Syntax 5-2: integral_number ::= decimal_number
  // decimal_number ::= unsigned_number
  auto v = RunAndGet(
      "module t;\n  logic [31:0] x;\n  initial x = 100;\nendmodule\n", "x");
  EXPECT_EQ(v, 100u);
}

// ---------------------------------------------------------------------------
// 3. number ::= integral_number — binary_number
// ---------------------------------------------------------------------------
TEST(SimCh5c, NumberIntegralBinary) {
  // Syntax 5-2: integral_number ::= binary_number
  auto v = RunAndGet(
      "module t;\n  logic [7:0] x;\n  initial x = 8'b1010_0101;\nendmodule\n",
      "x");
  EXPECT_EQ(v, 0xA5u);
}

// ---------------------------------------------------------------------------
// 4. number ::= integral_number — octal_number
// ---------------------------------------------------------------------------
TEST(SimCh5c, NumberIntegralOctal) {
  // Syntax 5-2: integral_number ::= octal_number
  auto v = RunAndGet(
      "module t;\n  logic [11:0] x;\n  initial x = 12'o7654;\nendmodule\n",
      "x");
  EXPECT_EQ(v, 07654u);
}

// ---------------------------------------------------------------------------
// 5. number ::= integral_number — hex_number
// ---------------------------------------------------------------------------
TEST(SimCh5c, NumberIntegralHex) {
  // Syntax 5-2: integral_number ::= hex_number
  auto v = RunAndGet(
      "module t;\n  logic [15:0] x;\n  initial x = 16'hCAFE;\nendmodule\n",
      "x");
  EXPECT_EQ(v, 0xCAFEu);
}

// ---------------------------------------------------------------------------
// 6. number ::= real_number — fixed_point_number
// ---------------------------------------------------------------------------
TEST(SimCh5c, NumberRealFixedPoint) {
  // Syntax 5-2: real_number ::= fixed_point_number
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 42.5;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 42.5);
}

// ---------------------------------------------------------------------------
// 7. number ::= real_number — scientific notation form
// ---------------------------------------------------------------------------
TEST(SimCh5c, NumberRealScientific) {
  // Syntax 5-2: real_number ::= unsigned_number [.unsigned_number] exp
  //                              [sign] unsigned_number
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 5.0e3;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 5000.0);
}

// ---------------------------------------------------------------------------
// 8. All four integral bases in one module
// ---------------------------------------------------------------------------
TEST(SimCh5c, NumberAllIntegralBases) {
  // §5.7 + Syntax 5-2: decimal, hex, octal, binary all work as number.
  SimCh5cFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, d;\n"
      "  initial begin\n"
      "    a = 255;\n"
      "    b = 8'hFF;\n"
      "    c = 8'o377;\n"
      "    d = 8'b1111_1111;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(design, nullptr);
  if (!design) return;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  auto* vc = f.ctx.FindVariable("c");
  auto* vd = f.ctx.FindVariable("d");
  EXPECT_NE(va, nullptr);
  EXPECT_NE(vb, nullptr);
  EXPECT_NE(vc, nullptr);
  EXPECT_NE(vd, nullptr);
  if (!va || !vb || !vc || !vd) return;
  EXPECT_EQ(va->value.ToUint64(), 255u);
  EXPECT_EQ(vb->value.ToUint64(), 255u);
  EXPECT_EQ(vc->value.ToUint64(), 255u);
  EXPECT_EQ(vd->value.ToUint64(), 255u);
}

// ---------------------------------------------------------------------------
// 9. Integer and real numbers in arithmetic expressions
// ---------------------------------------------------------------------------
TEST(SimCh5c, NumberMixedInExpression) {
  // §5.7: Both number forms usable in expression contexts.
  // Integer literal 10 used in expression assigned to logic; real 2.5 to real.
  SimCh5cFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] i;\n"
      "  real r;\n"
      "  initial begin\n"
      "    i = 10 + 20;\n"
      "    r = 1.5 + 2.5;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(design, nullptr);
  if (!design) return;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vi = f.ctx.FindVariable("i");
  auto* vr = f.ctx.FindVariable("r");
  EXPECT_NE(vi, nullptr);
  EXPECT_NE(vr, nullptr);
  if (!vi || !vr) return;
  EXPECT_EQ(vi->value.ToUint64(), 30u);
  double d = 0.0;
  uint64_t bits = vr->value.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  EXPECT_DOUBLE_EQ(d, 4.0);
}

// ---------------------------------------------------------------------------
// 10. number as primary_literal in conditional expression
// ---------------------------------------------------------------------------
TEST(SimCh5c, NumberAsPrimaryLiteralInTernary) {
  // Syntax 5-2: primary_literal ::= number | ...
  // Verify number works as primary_literal in ternary expression.
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 1 ? 8'd99 : 8'd0;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(v, 99u);
}

// ---------------------------------------------------------------------------
// 11. Sized decimal with base format
// ---------------------------------------------------------------------------
TEST(SimCh5c, NumberSizedDecimalBase) {
  // Syntax 5-2: decimal_number ::= [size] decimal_base unsigned_number
  auto v = RunAndGet(
      "module t;\n  logic [7:0] x;\n  initial x = 8'd200;\nendmodule\n", "x");
  EXPECT_EQ(v, 200u);
}

// ---------------------------------------------------------------------------
// 12. Underscore in integral number (Syntax 5-2 note 38)
// ---------------------------------------------------------------------------
TEST(SimCh5c, NumberUnderscoreInIntegral) {
  // Syntax 5-2: unsigned_number ::= decimal_digit { _ | decimal_digit }
  // "Embedded spaces are illegal" (note 38), but underscores are legal.
  auto v = RunAndGet(
      "module t;\n  logic [31:0] x;\n  initial x = 1_000_000;\nendmodule\n",
      "x");
  EXPECT_EQ(v, 1000000u);
}

// ===========================================================================
// §5.8 Time literals — simulation-level tests
//
// LRM §5.8: "Time is written in integer or fixed-point format, followed
// without a space by a time unit (fs ps ns us ms s)."
// "The time literal is interpreted as a realtime value scaled to the
// current time unit."
// ===========================================================================

// ---------------------------------------------------------------------------
// 1. Integer format with ns unit (default time unit)
// ---------------------------------------------------------------------------
TEST(SimCh5c, TimeLitIntegerNs) {
  // §5.8: "Time is written in integer ... format, followed without a space
  // by a time unit"  Example: 40ps.  Here we use ns (default unit).
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 10ns;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 10.0);
}

// ---------------------------------------------------------------------------
// 2. Fixed-point format with ns unit
// ---------------------------------------------------------------------------
TEST(SimCh5c, TimeLitFixedPointNs) {
  // §5.8: "Time is written in ... fixed-point format, followed without a
  // space by a time unit"  Example from LRM: 2.1ns.
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 2.1ns;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 2.1);
}

// ---------------------------------------------------------------------------
// 3. ps unit — scaled to default time unit (ns)
// ---------------------------------------------------------------------------
TEST(SimCh5c, TimeLitPs) {
  // §5.8 example: 40ps.  With default timeunit 1ns: 40ps = 0.04 ns.
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 40ps;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 0.04);
}

// ---------------------------------------------------------------------------
// 4. fs unit — scaled to default time unit (ns)
// ---------------------------------------------------------------------------
TEST(SimCh5c, TimeLitFs) {
  // §5.8 unit: fs.  100fs = 0.0001 ns.
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 100fs;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 0.0001);
}

// ---------------------------------------------------------------------------
// 5. us unit — scaled to default time unit (ns)
// ---------------------------------------------------------------------------
TEST(SimCh5c, TimeLitUs) {
  // §5.8 unit: us.  1us = 1000.0 ns.
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 1us;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 1000.0);
}

// ---------------------------------------------------------------------------
// 6. ms unit — scaled to default time unit (ns)
// ---------------------------------------------------------------------------
TEST(SimCh5c, TimeLitMs) {
  // §5.8 unit: ms.  1ms = 1e6 ns.
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 1ms;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 1e6);
}

// ---------------------------------------------------------------------------
// 7. s unit — scaled to default time unit (ns)
// ---------------------------------------------------------------------------
TEST(SimCh5c, TimeLitS) {
  // §5.8 unit: s.  1s = 1e9 ns.
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 1s;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 1e9);
}

// ---------------------------------------------------------------------------
// 8. Fixed-point format with non-ns unit
// ---------------------------------------------------------------------------
TEST(SimCh5c, TimeLitFixedPointUs) {
  // §5.8: fixed-point format with us unit.  2.5us = 2500.0 ns.
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 2.5us;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 2500.0);
}

// ---------------------------------------------------------------------------
// 9. LRM example: 2.1ns
// ---------------------------------------------------------------------------
TEST(SimCh5c, TimeLitLrmExample2p1ns) {
  // §5.8 example verbatim: "2.1ns"
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 2.1ns;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 2.1);
}

// ---------------------------------------------------------------------------
// 10. LRM example: 40ps
// ---------------------------------------------------------------------------
TEST(SimCh5c, TimeLitLrmExample40ps) {
  // §5.8 example verbatim: "40ps"
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 40ps;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 0.04);
}

// ===========================================================================
// §5.9.1 Special characters in strings — simulation-level tests
//
// LRM §5.9.1: Table 5-1 lists escape sequences for special characters in
// string literals.  An escaped character not in Table 5-1 "is treated the
// same as if the character was not escaped."
// ===========================================================================

// ---------------------------------------------------------------------------
// 1. \n — Newline character (0x0A)
// ---------------------------------------------------------------------------
TEST(SimCh5c, StrEscNewline) {
  // §5.9.1 Table 5-1: \n → newline character
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\n\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x0Au);
}

// ---------------------------------------------------------------------------
// 2. \t — Tab character (0x09)
// ---------------------------------------------------------------------------
TEST(SimCh5c, StrEscTab) {
  // §5.9.1 Table 5-1: \t → tab character
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\t\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x09u);
}

// ---------------------------------------------------------------------------
// 3. \\ — Backslash character (0x5C)
// ---------------------------------------------------------------------------
TEST(SimCh5c, StrEscBackslash) {
  // §5.9.1 Table 5-1: \\ → \ character
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\\\\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x5Cu);
}

// ---------------------------------------------------------------------------
// 4. \" — Double-quote character (0x22)
// ---------------------------------------------------------------------------
TEST(SimCh5c, StrEscDoubleQuote) {
  // §5.9.1 Table 5-1: \" → " character
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\\"\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x22u);
}

// ---------------------------------------------------------------------------
// 5. \v — Vertical tab (0x0B)
// ---------------------------------------------------------------------------
TEST(SimCh5c, StrEscVerticalTab) {
  // §5.9.1 Table 5-1: \v → vertical tab
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\v\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x0Bu);
}

// ---------------------------------------------------------------------------
// 6. \f — Form feed (0x0C)
// ---------------------------------------------------------------------------
TEST(SimCh5c, StrEscFormFeed) {
  // §5.9.1 Table 5-1: \f → form feed
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\f\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x0Cu);
}

// ---------------------------------------------------------------------------
// 7. \a — Bell (0x07)
// ---------------------------------------------------------------------------
TEST(SimCh5c, StrEscBell) {
  // §5.9.1 Table 5-1: \a → bell
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\a\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x07u);
}

// ---------------------------------------------------------------------------
// 8. \ddd — Octal escape, three digits
// ---------------------------------------------------------------------------
TEST(SimCh5c, StrEscOctalThreeDigit) {
  // §5.9.1 Table 5-1: \ddd → character specified in 1-3 octal digits.
  // \101 = 65 decimal = 'A'
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\101\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x41u);
}

// ---------------------------------------------------------------------------
// 9. \ddd — Octal escape, one digit
// ---------------------------------------------------------------------------
TEST(SimCh5c, StrEscOctalOneDigit) {
  // §5.9.1: 1-digit octal.  \7 = 7 = BEL.
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\7\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x07u);
}

// ---------------------------------------------------------------------------
// 10. \xdd — Hex escape, two digits
// ---------------------------------------------------------------------------
TEST(SimCh5c, StrEscHexTwoDigit) {
  // §5.9.1 Table 5-1: \xdd → character specified in 1-2 hex digits.
  // \x41 = 65 = 'A'
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\x41\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x41u);
}

// ---------------------------------------------------------------------------
// 11. \xd — Hex escape, one digit
// ---------------------------------------------------------------------------
TEST(SimCh5c, StrEscHexOneDigit) {
  // §5.9.1: 1-digit hex.  \xA = 10 = newline.
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\xA\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x0Au);
}

// ---------------------------------------------------------------------------
// 12. Unrecognized escape — treated as literal character
// ---------------------------------------------------------------------------
TEST(SimCh5c, StrEscUnrecognized) {
  // §5.9.1: "An escaped character not appearing in Table 5-1 is treated
  // the same as if the character was not escaped."  \b → 'b' (0x62).
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\b\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x62u);
}

// ---------------------------------------------------------------------------
// 13. Multiple escape sequences in one string
// ---------------------------------------------------------------------------
TEST(SimCh5c, StrEscMultiple) {
  // §5.9.1: Multiple escapes in a single string: "A\nB" → 3 bytes: 0x41
  // 0x0A 0x42 → packed 24-bit value 0x410A42.
  auto v = RunAndGet(
      "module t;\n  bit [23:0] s;\n  initial s = \"A\\nB\";\nendmodule\n", "s");
  EXPECT_EQ(v, 0x410A42u);
}

// ===========================================================================
// §5.7.2 Real literal constants — simulation-level tests
//
// LRM §5.7.2: "The real literal constant numbers shall be represented as
// described by IEEE Std 754, an IEEE standard for double-precision
// floating-point numbers."
// ===========================================================================

// ---------------------------------------------------------------------------
// 1. Fixed-point decimal notation
// ---------------------------------------------------------------------------
TEST(SimCh5c, RealFixedPointDecimal) {
  // §5.7.2: "Real numbers can be specified in … decimal notation
  // (for example, 14.72)"
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 1.2;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 1.2);
}

// ---------------------------------------------------------------------------
// 2. Small fixed-point value
// ---------------------------------------------------------------------------
TEST(SimCh5c, RealSmallFixedPoint) {
  // §5.7.2 valid form: "0.1"
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 0.1;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 0.1);
}

// ---------------------------------------------------------------------------
// 3. Large fixed-point value
// ---------------------------------------------------------------------------
TEST(SimCh5c, RealLargeFixedPoint) {
  // §5.7.2 valid form: "2394.26331"
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 2394.26331;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 2394.26331);
}

// ---------------------------------------------------------------------------
// 4. Scientific notation with uppercase E
// ---------------------------------------------------------------------------
TEST(SimCh5c, RealScientificUpperE) {
  // §5.7.2: "1.2E12 (the exponent symbol can be e or E)"
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 1.2E12;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 1.2e12);
}

// ---------------------------------------------------------------------------
// 5. Scientific notation with lowercase e and negative exponent
// ---------------------------------------------------------------------------
TEST(SimCh5c, RealScientificLowerENeg) {
  // §5.7.2 valid form: "1.30e-2"
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 1.30e-2;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 1.30e-2);
}

// ---------------------------------------------------------------------------
// 6. Scientific notation with zero exponent
// ---------------------------------------------------------------------------
TEST(SimCh5c, RealScientificZeroExponent) {
  // §5.7.2 valid form: "0.1e-0"
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 0.1e-0;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 0.1);
}

// ---------------------------------------------------------------------------
// 7. Integer with scientific notation (no decimal point)
// ---------------------------------------------------------------------------
TEST(SimCh5c, RealIntegerScientific) {
  // §5.7.2 valid form: "23E10"
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 23E10;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 23e10);
}

// ---------------------------------------------------------------------------
// 8. Integer with negative exponent
// ---------------------------------------------------------------------------
TEST(SimCh5c, RealIntegerNegativeExponent) {
  // §5.7.2 valid form: "29E-2"
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 29E-2;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 29e-2);
}

// ---------------------------------------------------------------------------
// 9. Underscores are ignored in real literals
// ---------------------------------------------------------------------------
TEST(SimCh5c, RealUnderscoreIgnored) {
  // §5.7.2: "236.123_763_e-12 (underscores are ignored)"
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 236.123_763_e-12;\nendmodule\n",
      "x");
  EXPECT_DOUBLE_EQ(v, 236.123763e-12);
}

// ---------------------------------------------------------------------------
// 10. Negative real via unary minus
// ---------------------------------------------------------------------------
TEST(SimCh5c, RealNegativeUnaryMinus) {
  // Unary minus applied to a real literal (§5.7.2 + §11.3).
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = -1.5;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, -1.5);
}

// ---------------------------------------------------------------------------
// 11. Scientific notation with explicit positive exponent sign
// ---------------------------------------------------------------------------
TEST(SimCh5c, RealExponentPositiveSign) {
  // §5.7.2 syntax: exp [ sign ] unsigned_number — sign can be '+'
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 1.0e+2;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 100.0);
}

// ---------------------------------------------------------------------------
// 12. IEEE 754 double-precision bit-exact storage
// ---------------------------------------------------------------------------
TEST(SimCh5c, RealIEEE754BitExact) {
  // §5.7.2: "represented as described by IEEE Std 754"
  // Verify the 64-bit pattern matches IEEE 754 double for 1.0.
  auto bits =
      RunAndGet("module t;\n  real x;\n  initial x = 1.0;\nendmodule\n", "x");
  uint64_t expected = 0x3FF0000000000000ULL;  // IEEE 754: 1.0
  EXPECT_EQ(bits, expected);
}

// ---------------------------------------------------------------------------
// 13. Real literal in arithmetic expression
// ---------------------------------------------------------------------------
TEST(SimCh5c, RealArithmeticExpression) {
  // Verify real arithmetic works end-to-end with literals.
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 1.5 + 2.25;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 3.75);
}

// ---------------------------------------------------------------------------
// 14. Real literal assigned to real variable preserves value
// ---------------------------------------------------------------------------
TEST(SimCh5c, RealVariablePreservesValue) {
  // §5.7.2: Verify round-trip through variable assignment.
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 3.14159265358979;\nendmodule\n",
      "x");
  EXPECT_DOUBLE_EQ(v, 3.14159265358979);
}

// ---------------------------------------------------------------------------
// 15. Large scientific notation value
// ---------------------------------------------------------------------------
TEST(SimCh5c, RealLargeScientific) {
  // §5.7.2 valid form: "39e8" (mentioned in spec text)
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 39e8;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 39e8);
}
