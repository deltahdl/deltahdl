
#include <cstring>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

// Helper: elaborate, lower, and run simulation. Returns true on success.
static bool RunSim(SimFixture& f, const std::string& src) {
  auto* design = ElaborateSrc(src, f);
  if (!design) return false;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return true;
}

static bool LowerRunAndFindIR(SimFixture& f, RtlirDesign* design,
                              Variable*& vi_out, Variable*& vr_out) {
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  vi_out = f.ctx.FindVariable("i");
  vr_out = f.ctx.FindVariable("r");
  EXPECT_NE(vi_out, nullptr);
  EXPECT_NE(vr_out, nullptr);
  return vi_out && vr_out;
}

// ===========================================================================
// §5.7 Numbers
// ===========================================================================

// ---------------------------------------------------------------------------
// 1. number ::= integral_number | real_number — both forms coexist
// ---------------------------------------------------------------------------
TEST(SimCh507, NumberBothFormsCoexist) {
  // §5.7: Both integer and real constants in the same module.
  SimFixture f;
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
  Variable* vi = nullptr;
  Variable* vr = nullptr;
  if (!LowerRunAndFindIR(f, design, vi, vr)) return;
  EXPECT_EQ(vi->value.ToUint64(), 42u);
  double d = 0.0;
  uint64_t bits = vr->value.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  EXPECT_DOUBLE_EQ(d, 3.14);
}

// ---------------------------------------------------------------------------
// 2. number ::= integral_number — decimal_number (unsigned_number form)
// ---------------------------------------------------------------------------
TEST(SimCh507, NumberIntegralDecimal) {
  // Syntax 5-2: integral_number ::= decimal_number
  // decimal_number ::= unsigned_number
  auto v = RunAndGet(
      "module t;\n  logic [31:0] x;\n  initial x = 100;\nendmodule\n", "x");
  EXPECT_EQ(v, 100u);
}

// ---------------------------------------------------------------------------
// 3. number ::= integral_number — binary_number
// ---------------------------------------------------------------------------
TEST(SimCh507, NumberIntegralBinary) {
  // Syntax 5-2: integral_number ::= binary_number
  auto v = RunAndGet(
      "module t;\n  logic [7:0] x;\n  initial x = 8'b1010_0101;\nendmodule\n",
      "x");
  EXPECT_EQ(v, 0xA5u);
}

// ---------------------------------------------------------------------------
// 4. number ::= integral_number — octal_number
// ---------------------------------------------------------------------------
TEST(SimCh507, NumberIntegralOctal) {
  // Syntax 5-2: integral_number ::= octal_number
  auto v = RunAndGet(
      "module t;\n  logic [11:0] x;\n  initial x = 12'o7654;\nendmodule\n",
      "x");
  EXPECT_EQ(v, 07654u);
}

// ---------------------------------------------------------------------------
// 5. number ::= integral_number — hex_number
// ---------------------------------------------------------------------------
TEST(SimCh507, NumberIntegralHex) {
  // Syntax 5-2: integral_number ::= hex_number
  auto v = RunAndGet(
      "module t;\n  logic [15:0] x;\n  initial x = 16'hCAFE;\nendmodule\n",
      "x");
  EXPECT_EQ(v, 0xCAFEu);
}

// ---------------------------------------------------------------------------
// 6. number ::= real_number — fixed_point_number
// ---------------------------------------------------------------------------
TEST(SimCh507, NumberRealFixedPoint) {
  // Syntax 5-2: real_number ::= fixed_point_number
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 42.5;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 42.5);
}

// ---------------------------------------------------------------------------
// 7. number ::= real_number — scientific notation form
// ---------------------------------------------------------------------------
TEST(SimCh507, NumberRealScientific) {
  // Syntax 5-2: real_number ::= unsigned_number [.unsigned_number] exp
  //                              [sign] unsigned_number
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 5.0e3;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 5000.0);
}

// ---------------------------------------------------------------------------
// 8. All four integral bases in one module
// ---------------------------------------------------------------------------
TEST(SimCh507, NumberAllIntegralBases) {
  // §5.7 + Syntax 5-2: decimal, hex, octal, binary all work as number.
  SimFixture f;
  ASSERT_TRUE(RunSim(f,
                     "module t;\n"
                     "  logic [7:0] a, b, c, d;\n"
                     "  initial begin\n"
                     "    a = 255;\n"
                     "    b = 8'hFF;\n"
                     "    c = 8'o377;\n"
                     "    d = 8'b1111_1111;\n"
                     "  end\n"
                     "endmodule\n"));
  const char* const kNames[] = {"a", "b", "c", "d"};
  for (const char* name : kNames) {
    auto* v = f.ctx.FindVariable(name);
    ASSERT_NE(v, nullptr) << name;
    EXPECT_EQ(v->value.ToUint64(), 255u) << name;
  }
}

// ---------------------------------------------------------------------------
// 9. Integer and real numbers in arithmetic expressions
// ---------------------------------------------------------------------------
TEST(SimCh507, NumberMixedInExpression) {
  // §5.7: Both number forms usable in expression contexts.
  // Integer literal 10 used in expression assigned to logic; real 2.5 to real.
  SimFixture f;
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
  Variable* vi = nullptr;
  Variable* vr = nullptr;
  if (!LowerRunAndFindIR(f, design, vi, vr)) return;
  EXPECT_EQ(vi->value.ToUint64(), 30u);
  double d = 0.0;
  uint64_t bits = vr->value.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  EXPECT_DOUBLE_EQ(d, 4.0);
}

// ---------------------------------------------------------------------------
// 10. number as primary_literal in conditional expression
// ---------------------------------------------------------------------------
TEST(SimCh507, NumberAsPrimaryLiteralInTernary) {
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
TEST(SimCh507, NumberSizedDecimalBase) {
  // Syntax 5-2: decimal_number ::= [size] decimal_base unsigned_number
  auto v = RunAndGet(
      "module t;\n  logic [7:0] x;\n  initial x = 8'd200;\nendmodule\n", "x");
  EXPECT_EQ(v, 200u);
}

// ---------------------------------------------------------------------------
// 12. Underscore in integral number (Syntax 5-2 note 38)
// ---------------------------------------------------------------------------
TEST(SimCh507, NumberUnderscoreInIntegral) {
  // Syntax 5-2: unsigned_number ::= decimal_digit { _ | decimal_digit }
  // Embedded spaces are illegal (note 38), but underscores are legal.
  auto v = RunAndGet(
      "module t;\n  logic [31:0] x;\n  initial x = 1_000_000;\nendmodule\n",
      "x");
  EXPECT_EQ(v, 1000000u);
}
