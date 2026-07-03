#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(ExpressionBitLength, TernaryWidthFromBranches) {
  SimFixture f;

  auto* cond = f.ctx.CreateVariable("tc", 1);
  cond->value = MakeLogic4VecVal(f.arena, 1, 1);
  auto* tv = f.ctx.CreateVariable("tv", 8);
  tv->value = MakeLogic4VecVal(f.arena, 8, 0xFF);
  auto* fv = f.ctx.CreateVariable("fv", 4);
  fv->value = MakeLogic4VecVal(f.arena, 4, 0xA);
  auto* tern = f.arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = MakeId(f.arena, "tc");
  tern->true_expr = MakeId(f.arena, "tv");
  tern->false_expr = MakeId(f.arena, "fv");
  auto result = EvalExpr(tern, f.ctx, f.arena);

  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
}

TEST(ExpressionBitLength, AssignmentContextWidthSameSize) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  logic [15:0] sumA;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    sumA = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sumA");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0000u);
}

TEST(ExpressionBitLength, CastingSetsContextWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  logic [15:0] answer;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    answer = (a + b + 0) >> 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("answer");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x8000u);
}

TEST(ExpressionBitLength, CastWidensIntermediateValue) {
  SimFixture f;
  MakeVar(f, "x", 4, 0xF);

  auto* cast = f.arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->text = "int";
  cast->lhs = MakeId(f.arena, "x");

  auto result = EvalExpr(cast, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
  EXPECT_EQ(result.ToUint64(), 0xFu);
}

TEST(ExpressionBitLength, CastWidensOperandPreservesCarry) {
  SimFixture f;
  MakeVar(f, "a", 4, 0xF);
  MakeVar(f, "b", 4, 1);

  auto* cast = f.arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->text = "int";
  cast->lhs = MakeId(f.arena, "a");

  auto* add = MakeBinary(f.arena, TokenKind::kPlus, cast, MakeId(f.arena, "b"));

  auto result = EvalExpr(add, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64(), 0x10u);
  EXPECT_EQ(result.width, 32u);
}

TEST(ExpressionBitLength, ShiftWidthIsLhsWidth) {
  SimFixture f;
  MakeVar(f, "sv", 8, 0xFF);
  MakeVar(f, "sh", 16, 2);

  for (TokenKind op : {TokenKind::kLtLt, TokenKind::kGtGt, TokenKind::kLtLtLt,
                       TokenKind::kGtGtGt}) {
    auto* expr =
        MakeBinary(f.arena, op, MakeId(f.arena, "sv"), MakeId(f.arena, "sh"));
    auto result = EvalExpr(expr, f.ctx, f.arena);
    EXPECT_EQ(result.width, 8u);
  }
}

TEST(ExpressionBitLength, PowerWidthIsBaseWidth) {
  SimFixture f;
  MakeVar(f, "base", 8, 3);
  MakeVar(f, "exp", 16, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeId(f.arena, "base"),
                          MakeId(f.arena, "exp"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 9u);
}

TEST(ExpressionBitLength, ReductionOpsProduceOneBit) {
  SimFixture f;
  MakeVar(f, "rv", 8, 0xFF);

  for (TokenKind op : {TokenKind::kAmp, TokenKind::kTildeAmp, TokenKind::kPipe,
                       TokenKind::kTildePipe, TokenKind::kCaret,
                       TokenKind::kTildeCaret, TokenKind::kCaretTilde}) {
    auto* expr = MakeUnary(f.arena, op, MakeId(f.arena, "rv"));
    auto result = EvalExpr(expr, f.ctx, f.arena);
    EXPECT_EQ(result.width, 1u);
  }
}

TEST(ExpressionBitLength, LogicalNotProducesOneBit) {
  SimFixture f;
  MakeVar(f, "nv", 16, 0);
  auto* expr = MakeUnary(f.arena, TokenKind::kBang, MakeId(f.arena, "nv"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ExpressionBitLength, LogicalAndOrProduceOneBit) {
  SimFixture f;
  MakeVar(f, "la", 16, 1);
  MakeVar(f, "lb", 8, 1);

  auto* and_expr = MakeBinary(f.arena, TokenKind::kAmpAmp,
                              MakeId(f.arena, "la"), MakeId(f.arena, "lb"));
  auto r1 = EvalExpr(and_expr, f.ctx, f.arena);
  EXPECT_EQ(r1.width, 1u);

  auto* or_expr = MakeBinary(f.arena, TokenKind::kPipePipe,
                             MakeId(f.arena, "la"), MakeId(f.arena, "lb"));
  auto r2 = EvalExpr(or_expr, f.ctx, f.arena);
  EXPECT_EQ(r2.width, 1u);
}

TEST(ExpressionBitLength, ImplicationAndEquivalenceProduceOneBit) {
  SimFixture f;
  MakeVar(f, "ia", 16, 1);
  MakeVar(f, "ib", 8, 0);

  auto* impl = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "ia"),
                          MakeId(f.arena, "ib"));
  auto r1 = EvalExpr(impl, f.ctx, f.arena);
  EXPECT_EQ(r1.width, 1u);
  EXPECT_EQ(r1.ToUint64(), 0u);

  auto* equiv = MakeBinary(f.arena, TokenKind::kLtDashGt, MakeId(f.arena, "ia"),
                           MakeId(f.arena, "ib"));
  auto r2 = EvalExpr(equiv, f.ctx, f.arena);
  EXPECT_EQ(r2.width, 1u);
  EXPECT_EQ(r2.ToUint64(), 0u);
}

TEST(ExpressionBitLength, ComparisonOpsProduceOneBit) {
  SimFixture f;
  MakeVar(f, "ca", 16, 5);
  MakeVar(f, "cb", 8, 5);

  for (TokenKind op : {TokenKind::kEqEq, TokenKind::kBangEq, TokenKind::kEqEqEq,
                       TokenKind::kBangEqEq, TokenKind::kLt, TokenKind::kGt,
                       TokenKind::kLtEq, TokenKind::kGtEq}) {
    auto* expr =
        MakeBinary(f.arena, op, MakeId(f.arena, "ca"), MakeId(f.arena, "cb"));
    auto result = EvalExpr(expr, f.ctx, f.arena);
    EXPECT_EQ(result.width, 1u);
  }
}

TEST(ExpressionBitLength, ShiftAmountIsSelfDetermined) {
  SimFixture f;
  MakeVar(f, "sd", 4, 0x8);
  MakeVar(f, "sa", 32, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kGtGt, MakeId(f.arena, "sd"),
                          MakeId(f.arena, "sa"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.ToUint64(), 4u);
}

TEST(ExpressionBitLength, TernaryConditionIsSelfDetermined) {
  SimFixture f;
  MakeVar(f, "tc32", 32, 1);
  MakeVar(f, "ttv", 4, 0xA);
  MakeVar(f, "tfv", 4, 0x5);

  auto* tern = f.arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = MakeId(f.arena, "tc32");
  tern->true_expr = MakeId(f.arena, "ttv");
  tern->false_expr = MakeId(f.arena, "tfv");
  auto result = EvalExpr(tern, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
}

TEST(ExpressionBitLength, ReplicationWidthIsCountTimesElement) {
  SimFixture f;
  MakeVar(f, "re", 8, 0xFF);
  auto* repl = f.arena.Create<Expr>();
  repl->kind = ExprKind::kReplicate;
  repl->repeat_count = MakeInt(f.arena, 3);
  repl->elements.push_back(MakeId(f.arena, "re"));
  auto result = EvalExpr(repl, f.ctx, f.arena);
  EXPECT_EQ(result.width, 24u);
}

TEST(ExpressionBitLength, UnsizedConstantLiteralYieldsAtLeast32Bits) {
  SimFixture f;
  auto* lit = MakeInt(f.arena, 42);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_GE(result.width, 32u);
}

TEST(ExpressionBitLength, SizedConstantLiteralYieldsGivenWidth) {
  SimFixture f;
  auto* lit = f.arena.Create<Expr>();
  lit->kind = ExprKind::kIntegerLiteral;
  lit->text = "8'hFF";
  lit->int_val = 0xFF;
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);
}

TEST(ExpressionBitLength, ArithmeticResultUsesMaxOperandWidth) {
  SimFixture f;
  MakeVar(f, "aw8", 8, 0xFF);
  MakeVar(f, "bw16", 16, 0x0001);
  for (TokenKind op : {TokenKind::kPlus, TokenKind::kMinus, TokenKind::kStar,
                       TokenKind::kSlash, TokenKind::kPercent, TokenKind::kAmp,
                       TokenKind::kPipe, TokenKind::kCaret,
                       TokenKind::kCaretTilde, TokenKind::kTildeCaret}) {
    auto* expr = MakeBinary(f.arena, op, MakeId(f.arena, "aw8"),
                            MakeId(f.arena, "bw16"));
    auto result = EvalExpr(expr, f.ctx, f.arena);
    EXPECT_EQ(result.width, 16u);
  }
}

TEST(ExpressionBitLength, UnaryPlusMinusTildePreserveOperandWidth) {
  SimFixture f;
  MakeVar(f, "uw", 12, 0x123);
  for (TokenKind op :
       {TokenKind::kPlus, TokenKind::kMinus, TokenKind::kTilde}) {
    auto* expr = MakeUnary(f.arena, op, MakeId(f.arena, "uw"));
    auto result = EvalExpr(expr, f.ctx, f.arena);
    EXPECT_EQ(result.width, 12u);
  }
}

TEST(ExpressionBitLength, ConcatenationResultIsSumOfOperandWidths) {
  SimFixture f;
  MakeVar(f, "cca", 8, 0xAA);
  MakeVar(f, "ccb", 16, 0xBBCC);
  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements = {MakeId(f.arena, "cca"), MakeId(f.arena, "ccb")};
  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(result.width, 24u);
}

TEST(ExpressionBitLength, LogicalAndOperandIsSelfDetermined) {
  SimFixture f;
  MakeVar(f, "laa", 16, 0xFFFF);
  MakeVar(f, "lab", 16, 0x0001);
  auto* add = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "laa"),
                         MakeId(f.arena, "lab"));
  auto* one = MakeInt(f.arena, 1);
  auto* land = MakeBinary(f.arena, TokenKind::kAmpAmp, add, one);
  auto result = EvalExpr(land, f.ctx, f.arena, 64);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(ExpressionBitLength, ReductionXorOperandIsSelfDetermined) {
  SimFixture f;
  MakeVar(f, "rxa", 16, 0xFFFF);
  MakeVar(f, "rxb", 16, 0x0001);
  auto* add = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "rxa"),
                         MakeId(f.arena, "rxb"));
  auto* xor_reduce = MakeUnary(f.arena, TokenKind::kCaret, add);
  auto result = EvalExpr(xor_reduce, f.ctx, f.arena, 64);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(ExpressionBitLength, ConcatenationOperandIsSelfDetermined) {
  SimFixture f;
  MakeVar(f, "csa", 16, 0xFFFF);
  MakeVar(f, "csb", 16, 0x0001);
  auto* add = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "csa"),
                         MakeId(f.arena, "csb"));
  auto* one_bit = f.arena.Create<Expr>();
  one_bit->kind = ExprKind::kIntegerLiteral;
  one_bit->text = "1'b1";
  one_bit->int_val = 1;
  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements = {add, one_bit};
  auto result = EvalExpr(concat, f.ctx, f.arena, 64);
  EXPECT_EQ(result.width, 17u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ExpressionBitLength, ReplicationElementIsSelfDetermined) {
  SimFixture f;
  MakeVar(f, "rea", 16, 0xFFFF);
  MakeVar(f, "reb", 16, 0x0001);
  auto* add = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "rea"),
                         MakeId(f.arena, "reb"));
  auto* repl = f.arena.Create<Expr>();
  repl->kind = ExprKind::kReplicate;
  repl->repeat_count = MakeInt(f.arena, 2);
  repl->elements.push_back(add);
  auto result = EvalExpr(repl, f.ctx, f.arena, 64);
  EXPECT_EQ(result.width, 32u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// Table 11-21, shift row: the result of a self-determined shift takes the bit
// length of its left operand (L(i)), so shifting a value left past that width
// drops the overflow bits. Built from a real declaration (an 8-bit operand,
// §11.5) and a sized literal (§5.7.1), driven through the full pipeline; with
// an equal-width target the operand's own width is what governs, isolating the
// L(i) rule from any wider assignment context.
TEST(ExpressionBitLength, ShiftResultTakesLeftOperandWidthEndToEnd) {
  EXPECT_EQ(RunAndGet("module m;\n"
                      "  logic [7:0] a;\n"
                      "  logic [7:0] r;\n"
                      "  initial begin\n"
                      "    a = 8'hFF;\n"
                      "    r = a << 4;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            0xF0u);
}

// Table 11-21, conditional row: i ? j : k has the bit length max(L(j),L(k)).
// The wider branch (8-bit) governs, so the narrower branch does not truncate
// the selected value. If the result were sized to the taken branch alone this
// would still read 0xC3, so the discriminating case is a value whose upper bits
// would be lost at the narrower width.
TEST(ExpressionBitLength, TernaryResultWidthIsMaxOfBranchesEndToEnd) {
  EXPECT_EQ(RunAndGet("module m;\n"
                      "  logic [7:0] wide;\n"
                      "  logic [3:0] narrow;\n"
                      "  logic [7:0] r;\n"
                      "  initial begin\n"
                      "    wide = 8'hC3;\n"
                      "    narrow = 4'h5;\n"
                      "    r = 1'b1 ? wide : narrow;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            0xC3u);
}

// Table 11-21, concatenation row: {i,...,j} has bit length L(i)+...+L(j) and
// each operand is self-determined. Here the operands are sized literals
// (§5.7.1) whose widths are "as given" (Table 11-21, sized constant row): a
// 4-bit and an 8-bit literal place into a 12-bit result, so the layout observes
// both the per-literal width and the summed concatenation width.
TEST(ExpressionBitLength, ConcatenationSumWidthDeterminesLayoutEndToEnd) {
  EXPECT_EQ(RunAndGet("module m;\n"
                      "  logic [11:0] r;\n"
                      "  initial r = {4'hA, 8'hBC};\n"
                      "endmodule\n",
                      "r"),
            0xABCu);
}

// Table 11-21, replication row: {i{j}} has bit length i*(L(j)). A 4-bit operand
// (a bit-select of a declared vector, §11.5) replicated three times yields a
// 12-bit result; the placement of every copy observes the count-times-inner
// width rule end to end.
TEST(ExpressionBitLength, ReplicationCountTimesInnerWidthEndToEnd) {
  EXPECT_EQ(RunAndGet("module m;\n"
                      "  logic [7:0] a;\n"
                      "  logic [11:0] r;\n"
                      "  initial begin\n"
                      "    a = 8'hFF;\n"
                      "    r = {3{a[3:0]}};\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            0xFFFu);
}

// Table 11-21, concatenation row, with net operands driven by a continuous
// assignment (§11.5 admits a net as an operand; this is the continuous-assign
// syntactic position rather than a procedural one). Two 8-bit nets concatenate
// into a 16-bit result whose layout observes the summed width end to end.
TEST(ExpressionBitLength, ConcatenationSumWidthOverNetOperandsEndToEnd) {
  EXPECT_EQ(RunAndGet("module m;\n"
                      "  wire [7:0] a = 8'hAA;\n"
                      "  wire [7:0] b = 8'hBB;\n"
                      "  wire [15:0] r;\n"
                      "  assign r = {a, b};\n"
                      "endmodule\n",
                      "r"),
            0xAABBu);
}

// Table 11-21, concatenation row, with a value parameter as an operand. A
// parameter (§6.20.2) has its own bit length that participates in the summed
// concatenation width, exercising the operand-is-a-parameter input form.
TEST(ExpressionBitLength, ConcatenationSumWidthWithParameterOperandEndToEnd) {
  EXPECT_EQ(RunAndGet("module m;\n"
                      "  parameter [7:0] P = 8'hC3;\n"
                      "  logic [3:0] a;\n"
                      "  logic [11:0] r;\n"
                      "  initial begin\n"
                      "    a = 4'h5;\n"
                      "    r = {P, a};\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            0xC35u);
}

// Table 11-21, concatenation row, observed in a declaration-initializer
// position (distinct lowering path from a procedural assignment). Sized
// literals (§5.7.1) keep their given widths (Table 11-21, sized constant row)
// and sum into the 12-bit initialized value.
TEST(ExpressionBitLength, ConcatenationSumWidthInDeclInitializerEndToEnd) {
  EXPECT_EQ(RunAndGet("module m;\n"
                      "  logic [11:0] r = {4'hA, 8'hBC};\n"
                      "endmodule\n",
                      "r"),
            0xABCu);
}

// Table 11-21, replication row, with the replication count supplied by a
// parameter constant expression (a different constant-evaluation path than a
// bare literal count). Three copies of a 4-bit operand form a 12-bit result.
TEST(ExpressionBitLength, ReplicationCountFromParameterEndToEnd) {
  EXPECT_EQ(RunAndGet("module m;\n"
                      "  parameter N = 3;\n"
                      "  logic [3:0] a;\n"
                      "  logic [11:0] r;\n"
                      "  initial begin\n"
                      "    a = 4'hA;\n"
                      "    r = {N{a}};\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            0xAAAu);
}

// Table 11-21, replication row, with the replication count supplied by a
// localparam constant expression. Same count-times-inner width rule, exercising
// the localparam constant form.
TEST(ExpressionBitLength, ReplicationCountFromLocalparamEndToEnd) {
  EXPECT_EQ(RunAndGet("module m;\n"
                      "  localparam M = 3;\n"
                      "  logic [3:0] a;\n"
                      "  logic [11:0] r;\n"
                      "  initial begin\n"
                      "    a = 4'hA;\n"
                      "    r = {M{a}};\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            0xAAAu);
}

// Table 11-21, arithmetic row: i op j takes bit length max(L(i),L(j)). Built
// from two declared operands of DIFFERING widths (§11.5), the wider 8-bit
// operand governs, so the add is performed in 8 bits and does not collapse to
// the narrower operand's width: 0x1F + 0x1 = 0x20. If the narrower operand's
// 4-bit width were used the sum would truncate to 0x00, so the value
// discriminates the max-width rule.
TEST(ExpressionBitLength, ArithmeticMaxWidthOverDifferingOperandsEndToEnd) {
  EXPECT_EQ(RunAndGet("module m;\n"
                      "  logic [7:0] a;\n"
                      "  logic [3:0] b;\n"
                      "  logic [7:0] r;\n"
                      "  initial begin\n"
                      "    a = 8'h1F;\n"
                      "    b = 4'h1;\n"
                      "    r = a + b;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            0x20u);
}

}  // namespace
