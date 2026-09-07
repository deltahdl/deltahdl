#include "fixture_real.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Elaborates and runs a module with two ints `x` and `y` whose `initial` block
// body is `body`, then returns the resolved `x` and `y` variables (both
// asserted non-null). Used by the prefix/postfix inc/dec return-value tests
// that differ only in the body and expected values.
static void RunXYBody(SimFixture& f, const std::string& body, Variable** vx,
                      Variable** vy) {
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  initial begin " +
          body +
          " end\n"
          "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  *vx = f.ctx.FindVariable("x");
  *vy = f.ctx.FindVariable("y");
  ASSERT_NE(*vx, nullptr);
  ASSERT_NE(*vy, nullptr);
}

TEST(ExpressionSim, PrefixIncrement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd5; ++x; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

TEST(ExpressionSim, PrefixDecrement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd10; --x; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

TEST(ExpressionSim, PostfixIncrement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd5; x++; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

TEST(ExpressionSim, PostfixDecrement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd10; x--; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

TEST(ExpressionSim, PrefixIncReturnsNewValue) {
  SimFixture f;
  Variable *vx = nullptr, *vy = nullptr;
  RunXYBody(f, "x = 5; y = ++x;", &vx, &vy);
  EXPECT_EQ(vx->value.ToUint64(), 6u);
  EXPECT_EQ(vy->value.ToUint64(), 6u);
}

TEST(ExpressionSim, PostfixIncReturnsOldValue) {
  SimFixture f;
  Variable *vx = nullptr, *vy = nullptr;
  RunXYBody(f, "x = 5; y = x++;", &vx, &vy);
  EXPECT_EQ(vx->value.ToUint64(), 6u);
  EXPECT_EQ(vy->value.ToUint64(), 5u);
}

TEST(ExpressionSim, PrefixDecReturnsNewValue) {
  SimFixture f;
  Variable *vx = nullptr, *vy = nullptr;
  RunXYBody(f, "x = 10; y = --x;", &vx, &vy);
  EXPECT_EQ(vx->value.ToUint64(), 9u);
  EXPECT_EQ(vy->value.ToUint64(), 9u);
}

TEST(ExpressionSim, PostfixDecReturnsOldValue) {
  SimFixture f;
  Variable *vx = nullptr, *vy = nullptr;
  RunXYBody(f, "x = 10; y = x--;", &vx, &vy);
  EXPECT_EQ(vx->value.ToUint64(), 9u);
  EXPECT_EQ(vy->value.ToUint64(), 10u);
}

// §11.4.2 states inc/dec behave as blocking assignments. Building the setup
// from the §10.4.1 blocking-assignment `=` and driving it through the full
// pipeline: the standalone `x++` completes before the next statement runs, so
// the later blocking read `y = x` observes the updated value in the same time
// step. A non-blocking (deferred) update would leave y at the pre-increment
// value.
TEST(ExpressionSim, IncrementActsAsBlockingAssignment) {
  SimFixture f;
  Variable *vx = nullptr, *vy = nullptr;
  RunXYBody(f, "x = 5; x++; y = x;", &vx, &vy);
  EXPECT_EQ(vx->value.ToUint64(), 6u);
  EXPECT_EQ(vy->value.ToUint64(), 6u);
}

// §11.4.2: the operators need no parentheses in an expression. Here `x++` is an
// operand of a binary `+` with no parentheses; at runtime the postfix form
// contributes the pre-increment value (5) to the sum while x itself advances to
// 6. Observes the no-paren rule producing correct arithmetic, not just an AST
// shape.
TEST(ExpressionSim, PostfixIncrementInBinaryExprUsesOldValue) {
  SimFixture f;
  Variable *vx = nullptr, *vy = nullptr;
  RunXYBody(f, "x = 5; y = x++ + 10;", &vx, &vy);
  EXPECT_EQ(vx->value.ToUint64(), 6u);
  EXPECT_EQ(vy->value.ToUint64(), 15u);
}

// §11.4.2 increment used in a for-loop step, exercised at runtime: each
// iteration applies `i++`, so after the loop i has advanced by 1 per iteration
// (reaching the bound) and the body has run the matching number of times.
TEST(ExpressionSim, IncrementDrivesForLoopIteration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int i, count;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "    for (i = 0; i < 4; i++) count = count + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vi = f.ctx.FindVariable("i");
  auto* vcount = f.ctx.FindVariable("count");
  ASSERT_NE(vi, nullptr);
  ASSERT_NE(vcount, nullptr);
  EXPECT_EQ(vi->value.ToUint64(), 4u);
  EXPECT_EQ(vcount->value.ToUint64(), 4u);
}

// Elaborates and runs a module with two `real` variables `rv` and `res` whose
// `initial` block body is `body`, then reports their final values as doubles.
// The `real` declaration and real-literal initializer are the production
// storage/read path, so inc/dec runs on a genuinely produced real operand
// rather than a hand-assembled one. `res` captures the operator's return value
// so the prefix (new) / postfix (old) distinction is observable alongside the
// §11.4.2 "adjust real operands by 1.0" rule.
static void RunRealBody(SimFixture& f, const std::string& body, double* rv,
                        double* res) {
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real rv, res;\n"
      "  initial begin " +
          body +
          " end\n"
          "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vrv = f.ctx.FindVariable("rv");
  auto* vres = f.ctx.FindVariable("res");
  ASSERT_NE(vrv, nullptr);
  ASSERT_NE(vres, nullptr);
  *rv = VecToDouble(vrv->value);
  *res = VecToDouble(vres->value);
}

// Prefix ++ on a real adds 1.0 to the operand and yields the incremented value.
TEST(RealIncDecSim, PrefixIncrementBy1Point0) {
  SimFixture f;
  double rv = 0.0, res = 0.0;
  RunRealBody(f, "rv = 2.5; res = ++rv;", &rv, &res);
  EXPECT_DOUBLE_EQ(rv, 3.5);
  EXPECT_DOUBLE_EQ(res, 3.5);
}

// Prefix -- on a real subtracts 1.0 and yields the decremented value.
TEST(RealIncDecSim, PrefixDecrementBy1Point0) {
  SimFixture f;
  double rv = 0.0, res = 0.0;
  RunRealBody(f, "rv = 2.5; res = --rv;", &rv, &res);
  EXPECT_DOUBLE_EQ(rv, 1.5);
  EXPECT_DOUBLE_EQ(res, 1.5);
}

// Postfix ++ on a real adds 1.0 to the operand but yields the value from before
// the increment.
TEST(RealIncDecSim, PostfixIncrementBy1Point0) {
  SimFixture f;
  double rv = 0.0, res = 0.0;
  RunRealBody(f, "rv = 4.0; res = rv++;", &rv, &res);
  EXPECT_DOUBLE_EQ(rv, 5.0);
  EXPECT_DOUBLE_EQ(res, 4.0);
}

// Postfix -- on a real subtracts 1.0 but yields the value from before.
TEST(RealIncDecSim, PostfixDecrementBy1Point0) {
  SimFixture f;
  double rv = 0.0, res = 0.0;
  RunRealBody(f, "rv = 4.0; res = rv--;", &rv, &res);
  EXPECT_DOUBLE_EQ(rv, 3.0);
  EXPECT_DOUBLE_EQ(res, 4.0);
}

// §11.4.2 makes these operators blocking assignments, so §10.4's list of
// left-hand sides governs them. Every case above increments a plain identifier,
// which is one of two forms the evaluator wrote; the rest were incremented by
// nothing at all and reported nothing.

// An unpacked array element.
TEST(ExpressionSim, IncrementWritesAnUnpackedArrayElement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int arr [0:3];\n"
      "  initial begin arr[2] = 10; arr[2]++; end\n"
      "endmodule\n",
      f, "arr[2]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

// A bit-select of a packed variable, whose other bits stand.
TEST(ExpressionSim, IncrementWritesABitSelect) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  initial begin d = 8'h00; d[3]++; end\n"
      "endmodule\n",
      f, "d");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x08u);
}

// A part-select, loaded first so the high nibble standing is part of the
// reading.
TEST(ExpressionSim, IncrementWritesAPartSelect) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  initial begin d = 8'hF0; d[3:0]++; end\n"
      "endmodule\n",
      f, "d");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xF1u);
}

// A packed struct member, which had no arm at all. The neighbouring member is
// in the same reading, a write that took the whole variable reaching it.
TEST(ExpressionSim, DecrementWritesAStructMember) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } pair_t;\n"
      "  pair_t s;\n"
      "  initial begin s.hi = 4'd2; s.lo = 4'd5; s.lo--; end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x24u);
}

// §11.4.1's once-only left-hand index rule, which §11.4.2 inherits by making
// these blocking assignments. The writers added above each re-derive the target
// from the index, so without a snapshot the count rises with them; the value is
// the same however many times a function returning a constant runs, which is
// why the count is what discriminates.
TEST(ExpressionSim, IncrementEvaluatesItsIndexOnce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:3];\n"
      "  int idx_calls;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return 2;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    arr[2] = 10;\n"
      "    idx_calls = 0;\n"
      "    arr[idx_fn()]++;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"arr[2]", 11u}, {"idx_calls", 1u}});
}

// §11.4.2 states that the increment and decrement operators "behave as blocking
// assignments", and §11.4.1 states that an assignment operator "is semantically
// equivalent to a blocking assignment", so `i++` and `i += 1` are one
// assignment of one arithmetic result and §11.4.3 governs both alike: "for the
// arithmetic operators, if any operand bit value is the unknown value x or the
// high-impedance value z, then the entire result value shall be x". The
// increment computed its new value as a uint64_t round-trip through
// Logic4Vec::ToUint64, which projects `aval & ~bval` and so reads an x or a z
// as a 0 and hands back a value every bit of which is known. The readings below
// are of what that projection lost, and each takes its result from the words
// rather than from ToUint64, which can express neither an unknown nor a bit
// above 63.

// Elaborates and runs a module whose module items are `decls` and whose
// `initial` block body is `body`, then returns the variable `name` the run left
// behind. The unknown-propagation readings differ only in those three.
static Variable* RunIncDecBody(SimFixture& f, const std::string& decls,
                               const std::string& body, const char* name) {
  return RunAndFindVar("module t;\n  " + decls + "\n  initial begin " + body +
                           " end\nendmodule\n",
                       f, name);
}

// An `integer` is 4-state, so an all-x operand reaches the increment intact and
// §11.4.3 makes the whole of the result x. Reading the x bits as 0 and adding 1
// to them left i at a known 1.
TEST(ExpressionSim, IncrementOfAnUnknownYieldsAnUnknown) {
  SimFixture f;
  auto* var = RunIncDecBody(f, "integer i;", "i = 'x; i++;", "i");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.words[0].aval & 0xFFFFFFFFu, 0xFFFFFFFFu);
  EXPECT_EQ(var->value.words[0].bval & 0xFFFFFFFFu, 0xFFFFFFFFu);
}

// The decrement is the same operand and the same rule, and it is a separate
// reading because it reaches EvalBinaryOp with a different token. Subtracting 1
// from the projected 0 wrapped, so i read 32'hFFFFFFFF with every bit known.
TEST(ExpressionSim, DecrementOfAnUnknownYieldsAnUnknown) {
  SimFixture f;
  auto* var = RunIncDecBody(f, "integer i;", "i = 'x; i--;", "i");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), std::string(32, 'x'));
}

// §11.4.3 makes the ENTIRE result x, not the one bit that was x. The operand
// holds a single unknown in bit 0 and seven known bits above it; the projection
// read that operand as 8'h04 and produced 8'h05, a result seven bits of which
// stood and the eighth of which had lost its x.
TEST(ExpressionSim,
     IncrementOfAPartlyUnknownOperandYieldsAnEntirelyUnknownResult) {
  SimFixture f;
  auto* var = RunIncDecBody(f, "logic [7:0] p;", "p = 8'b0000_010x; p++;", "p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0xFFu, 0xFFu);
  EXPECT_EQ(var->value.words[0].bval & 0xFFu, 0xFFu);
}

// The §11.4.2 and §11.4.1 equality itself: the two spellings of adding one are
// one assignment of one arithmetic result, so they cannot answer differently
// about the same operand. `j += 1` already went through EvalBinaryOp and
// yielded an unknown while `i++` went through the projection and yielded a
// known 1, so the two disagreed on identical inputs.
TEST(ExpressionSim, IncrementAndCompoundAddAgreeOnAnUnknown) {
  SimFixture f;
  auto* vi =
      RunIncDecBody(f, "integer i, j;", "i = 'x; j = 'x; i++; j += 1;", "i");
  ASSERT_NE(vi, nullptr);
  auto* vj = f.ctx.FindVariable("j");
  ASSERT_NE(vj, nullptr);
  EXPECT_FALSE(vi->value.IsKnown());
  EXPECT_EQ(vi->value.ToString(), vj->value.ToString());
}

// HasUnknownBits scans every word and MakeAllX fills every word, so the unknown
// operand is recognized and the unknown result is written above bit 63 as well
// as below it. ToUint64 reads words[0] alone, so the projection produced a
// 128-bit value whose high word was zero and every bit of which was known.
TEST(ExpressionSim, IncrementOfAWideUnknownIsUnknownAboveTheFirstWord) {
  SimFixture f;
  auto* var = RunIncDecBody(f, "logic [127:0] w;", "w = 'x; w++;", "w");
  ASSERT_NE(var, nullptr);
  ASSERT_GE(var->value.nwords, 2u);
  EXPECT_NE(var->value.words[1].bval, 0u);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

// The postfix form returns the operand's value from before the increment, which
// was read straight off the variable and so was already unknown; what the
// projection changed is the variable the same statement writes. `y = x++` left
// y unknown and x at a known 1, an increment and its own return value
// disagreeing about whether the operand was ever unknown.
TEST(ExpressionSim, PostfixIncrementOfAnUnknownReturnsTheUnknownOldValue) {
  SimFixture f;
  auto* vy = RunIncDecBody(f, "integer x, y;", "x = 'x; y = x++;", "y");
  ASSERT_NE(vy, nullptr);
  auto* vx = f.ctx.FindVariable("x");
  ASSERT_NE(vx, nullptr);
  EXPECT_FALSE(vy->value.IsKnown());
  EXPECT_FALSE(vx->value.IsKnown());
}

}  // namespace
