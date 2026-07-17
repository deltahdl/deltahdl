#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"

using namespace delta;

// Clause 11.8.4 "Handling x and z in signed expressions". Three runtime rules,
// all owned here:
//   (A) When a signed operand is resized to a larger signed width and its sign
//       bit is x, the widened high bits are bit-filled with x.
//   (B) When the sign bit is z, the widened high bits are bit-filled with z.
//   (C) When any bit of a signed value is x or z, any nonlogical operation on
//       that value yields an entirely-x result whose type stays consistent with
//       the expression's type.
//
// These are simulator-stage rules; there is no BNF, no parse/elaborate 'shall'.
// Rules (A)/(B) are carried by two distinct production widening helpers:
// SignExtendWideResult (statement_assign.cpp, the assignment resize path) and
// ApplySignFill/ExtendVec (evaluation_ops.cpp, the expression-widening path).
// Rule (C) is carried by the arithmetic evaluator (evaluation_ops.cpp), which
// short-circuits to MakeAllX and keeps result.is_signed when either operand
// carries unknown bits.
//
// The rules' behavior depends on how the operand is produced: a value is only
// governed by these rules when it is signed (a `logic signed` declaration) and
// when its sign bit or some bit holds x or z (a 4-state literal such as
// 4'bx111). So each test builds the operand from real source and drives it
// through the full pipeline (parse, elaborate, lower, run), then inspects the
// raw 4-state words because $display-free value inspection via ToUint64 would
// collapse x/z to 0. In this codebase's encoding a known 0 is a=0/b=0, known 1
// is a=1/b=0, x is a=1/b=1, and z is a=0/b=1; so b (bval) flags "unknown" and,
// among unknown bits, a (aval) distinguishes x (a=1) from z (a=0).

namespace {

// Elaborate/lower/run `src` and return the final value of variable `name`.
Logic4Vec RunVar(const std::string& src, const char* name, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return {};
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable(name);
  EXPECT_NE(var, nullptr);
  return var ? var->value : Logic4Vec{};
}

// (A) Assignment resize path: a signed narrow source whose sign bit is x, when
// assigned into a wider signed target, fills the widened high bits with x.
TEST(SignedXZ, AssignWidenSignBitXFillsWithXEndToEnd) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] b;\n"
      "  logic signed [7:0] a;\n"
      "  initial begin\n"
      "    b = 4'bx111;\n"  // sign bit x, low bits known 1
      "    a = b;\n"        // widen 4 -> 8 signed: high nibble filled with x
      "  end\n"
      "endmodule\n",
      "a", f);
  // x fill means both aval and bval set across the widened high nibble.
  EXPECT_EQ(v.words[0].bval & 0xF0u, 0xF0u);
  EXPECT_EQ(v.words[0].aval & 0xF0u, 0xF0u);
}

// (B) Assignment resize path: sign bit z fills the widened high bits with z,
// distinguished from x by aval staying clear where bval is set.
TEST(SignedXZ, AssignWidenSignBitZFillsWithZEndToEnd) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] b;\n"
      "  logic signed [7:0] a;\n"
      "  initial begin\n"
      "    b = 4'bz111;\n"  // sign bit z
      "    a = b;\n"        // widen 4 -> 8 signed: high nibble filled with z
      "  end\n"
      "endmodule\n",
      "a", f);
  // z fill: bval set, aval clear across the widened high nibble.
  EXPECT_EQ(v.words[0].bval & 0xF0u, 0xF0u);
  EXPECT_EQ(v.words[0].aval & 0xF0u, 0x00u);
}

// (A) Expression-widening path: a ternary result width is the wider of its
// branches, so selecting the narrow signed branch widens it inside the
// expression evaluator (ExtendVec), independent of the assignment resize. An x
// sign bit fills with x there too.
TEST(SignedXZ, TernaryWidenSignBitXFillsWithXEndToEnd) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] s;\n"
      "  logic signed [7:0] w;\n"
      "  logic signed [7:0] r;\n"
      "  initial begin\n"
      "    s = 4'bx111;\n"
      "    w = 0;\n"
      "    r = 1'b1 ? s : w;\n"  // result width 8; s widened signed -> x fill
      "  end\n"
      "endmodule\n",
      "r", f);
  EXPECT_EQ(v.words[0].bval & 0xF0u, 0xF0u);
  EXPECT_EQ(v.words[0].aval & 0xF0u, 0xF0u);
}

// (B) Expression-widening path with a z sign bit.
TEST(SignedXZ, TernaryWidenSignBitZFillsWithZEndToEnd) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] s;\n"
      "  logic signed [7:0] w;\n"
      "  logic signed [7:0] r;\n"
      "  initial begin\n"
      "    s = 4'bz111;\n"
      "    w = 0;\n"
      "    r = 1'b1 ? s : w;\n"
      "  end\n"
      "endmodule\n",
      "r", f);
  EXPECT_EQ(v.words[0].bval & 0xF0u, 0xF0u);
  EXPECT_EQ(v.words[0].aval & 0xF0u, 0x00u);
}

// Negative for (A)/(B): the x/z-fill rules apply only when the sign bit is x or
// z. A known (here negative) sign bit widens by ordinary sign extension and
// fabricates no unknown bits, so no x/z fill occurs.
TEST(SignedXZ, KnownSignBitWidensWithoutUnknownFill) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] b;\n"
      "  logic signed [7:0] a;\n"
      "  initial begin\n"
      "    b = -1;\n"  // sign bit known 1
      "    a = b;\n"   // widen 4 -> 8 signed: high nibble filled with known 1
      "  end\n"
      "endmodule\n",
      "a", f);
  EXPECT_EQ(v.words[0].bval & 0xFFu, 0x00u);  // no unknown bits produced
  EXPECT_EQ(v.words[0].aval & 0xF0u, 0xF0u);  // ordinary sign extension of 1
}

// (A) The x-fill rule governs "an assignment" at any procedural position, not
// only blocking assignment. A nonblocking assignment of a narrower signed
// source whose sign bit is x reaches the same resize helper and fills the
// widened high bits with x once the NBA update settles.
TEST(SignedXZ, AssignWidenSignBitXFillsThroughNonblocking) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] b;\n"
      "  logic signed [7:0] a;\n"
      "  initial begin\n"
      "    b = 4'bx111;\n"
      "    a <= b;\n"  // nonblocking widen 4 -> 8 signed: high nibble x
      "  end\n"
      "endmodule\n",
      "a", f);
  EXPECT_EQ(v.words[0].bval & 0xF0u, 0xF0u);
  EXPECT_EQ(v.words[0].aval & 0xF0u, 0xF0u);
}

// (A) A continuous assignment widens its driven signed value through the same
// resize helper: driving a narrower signed source with an x sign bit onto a
// wider signed target fills the widened high bits with x.
TEST(SignedXZ, AssignWidenSignBitXFillsThroughContinuousAssign) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] b;\n"
      "  logic signed [7:0] a;\n"
      "  assign a = b;\n"  // continuous widen 4 -> 8 signed
      "  initial b = 4'bx111;\n"
      "endmodule\n",
      "a", f);
  EXPECT_EQ(v.words[0].bval & 0xF0u, 0xF0u);
  EXPECT_EQ(v.words[0].aval & 0xF0u, 0xF0u);
}

// (A) Bit-filling with x spans every widened word, not just the first. A signed
// source resized past a 64-bit word boundary x-fills the entire high portion,
// including a whole upper word (exercises the multi-word fill path).
TEST(SignedXZ, WideSignBitXFillsAcrossMultipleWords) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [39:0] b;\n"
      "  logic signed [95:0] a;\n"
      "  initial begin\n"
      "    b = 40'bx;\n"  // 40-bit all-x, sign bit x
      "    a = b;\n"      // widen 40 -> 96 signed: fill spans the upper word
      "  end\n"
      "endmodule\n",
      "a", f);
  // The whole upper word (bits 64-95) is filled with x.
  EXPECT_EQ(v.words[1].bval & 0xFFFFFFFFu, 0xFFFFFFFFu);
  EXPECT_EQ(v.words[1].aval & 0xFFFFFFFFu, 0xFFFFFFFFu);
}

// (C) A signed operand carrying x drives an addition (a nonlogical operation)
// to an entirely-x result at the full expression width.
TEST(SignedXZ, SignedAdditionWithXBitYieldsAllX) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] a, b, r;\n"
      "  initial begin\n"
      "    a = 4'b010x;\n"  // one x bit
      "    b = 4'd1;\n"
      "    r = a + b;\n"
      "  end\n"
      "endmodule\n",
      "r", f);
  EXPECT_EQ(v.words[0].aval & 0xFu, 0xFu);
  EXPECT_EQ(v.words[0].bval & 0xFu, 0xFu);
}

// (C) Multiplication with a z bit likewise yields an entirely-x result — z, not
// only x, triggers the rule.
TEST(SignedXZ, SignedMultiplicationWithZBitYieldsAllX) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] a, b, r;\n"
      "  initial begin\n"
      "    a = 4'b010z;\n"  // one z bit
      "    b = 4'd2;\n"
      "    r = a * b;\n"
      "  end\n"
      "endmodule\n",
      "r", f);
  EXPECT_EQ(v.words[0].aval & 0xFu, 0xFu);
  EXPECT_EQ(v.words[0].bval & 0xFu, 0xFu);
}

// (C) The power operator is a nonlogical operation as well.
TEST(SignedXZ, SignedPowerWithXBitYieldsAllX) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] a, b, r;\n"
      "  initial begin\n"
      "    a = 4'b011x;\n"
      "    b = 4'd2;\n"
      "    r = a ** b;\n"
      "  end\n"
      "endmodule\n",
      "r", f);
  EXPECT_EQ(v.words[0].aval & 0xFu, 0xFu);
  EXPECT_EQ(v.words[0].bval & 0xFu, 0xFu);
}

// (C) A unary nonlogical operation (arithmetic negation) on an x-bearing signed
// value is also entirely x.
TEST(SignedXZ, UnaryMinusOnXSignedYieldsAllX) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] a, r;\n"
      "  initial begin\n"
      "    a = 4'b010x;\n"
      "    r = -a;\n"
      "  end\n"
      "endmodule\n",
      "r", f);
  EXPECT_EQ(v.words[0].aval & 0xFu, 0xFu);
  EXPECT_EQ(v.words[0].bval & 0xFu, 0xFu);
}

// (C) "the entire resultant value being an x" also covers operations that
// produce a 1-bit result: a relational comparison of an x-bearing signed value
// yields a single x bit.
TEST(SignedXZ, RelationalWithXYieldsSingleXBit) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b010x;\n"
      "    b = 4'd1;\n"
      "    r = a < b;\n"
      "  end\n"
      "endmodule\n",
      "r", f);
  EXPECT_EQ(v.width, 1u);
  EXPECT_NE(v.words[0].bval & 0x1u, 0u);  // the one result bit is unknown
}

// Negative for (C): with no x or z bit present, the same signed nonlogical
// operation computes its ordinary arithmetic result rather than collapsing to
// all-x.
TEST(SignedXZ, KnownSignedNonlogicalOpNotAllX) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] a, b, r;\n"
      "  initial begin\n"
      "    a = 4'd5;\n"
      "    b = 4'd2;\n"
      "    r = a - b;\n"
      "  end\n"
      "endmodule\n",
      "r", f);
  EXPECT_EQ(v.words[0].bval & 0xFu, 0x0u);  // no unknown bits
  EXPECT_EQ(v.words[0].aval & 0xFu, 0x3u);  // 5 - 2 = 3
}

// The rule is scoped to *nonlogical* operations. A logical (here bitwise)
// operation where a known operand determines each result bit is not subject to
// the all-x collapse: x AND 0 is a known 0, so an x-bearing operand ANDed with
// zero stays fully defined.
TEST(SignedXZ, BitwiseAndWithZeroStaysDefinedDespiteX) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] a, r;\n"
      "  initial begin\n"
      "    a = 4'b010x;\n"
      "    r = a & 4'b0000;\n"
      "  end\n"
      "endmodule\n",
      "r", f);
  EXPECT_EQ(v.words[0].bval & 0xFu, 0x0u);  // stays defined, not all-x
  EXPECT_EQ(v.words[0].aval & 0xFu, 0x0u);
}

}  // namespace
