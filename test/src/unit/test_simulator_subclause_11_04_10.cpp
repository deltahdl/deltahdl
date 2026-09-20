#include <gtest/gtest.h>

#include <initializer_list>
#include <string>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "lexer/token.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(EvalOpXZ, ShiftXAmount) {
  SimFixture f;

  MakeVar4(f, "sa", 4, 0b0000, 0b0100);
  auto* a = f.ctx.CreateVariable("sv", 4);
  a->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtLt, MakeId(f.arena, "sv"),
                          MakeId(f.arena, "sa"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ShiftLeftXOperand) {
  SimFixture f;

  MakeVar4(f, "so", 4, 0b1000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtLt, MakeId(f.arena, "so"),
                          MakeInt(f.arena, 1));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.words[0].aval & 0xFu, 0b0000u);
  EXPECT_EQ(result.words[0].bval & 0xFu, 0b1000u);
}

TEST(ExpressionSim, LeftShift) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd1 << 3;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

TEST(ExpressionSim, RightShift) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd16 >> 2;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(OperatorSim, BinaryArithLeftShift) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd3 <<< 2;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 12u);
}

TEST(OperatorSim, BinaryArithRightShift) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd64 >>> 2;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(OperatorSim, ArithRightShiftUnsignedZeroFills) {
  SimFixture f;

  MakeVar(f, "u", 4, 0b1000);
  auto* expr = MakeBinary(f.arena, TokenKind::kGtGtGt, MakeId(f.arena, "u"),
                          MakeInt(f.arena, 2));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64() & 0xFu, 0b0010u);
}

TEST(EvalOpXZ, ArithRightShiftXAmount) {
  SimFixture f;
  MakeVar(f, "v", 4, 0b1100);
  MakeVar4(f, "sa", 4, 0b0000, 0b0010);
  auto* expr = MakeBinary(f.arena, TokenKind::kGtGtGt, MakeId(f.arena, "v"),
                          MakeId(f.arena, "sa"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalRightShiftXAmount) {
  SimFixture f;
  MakeVar(f, "v", 4, 0b1100);
  MakeVar4(f, "sa", 4, 0b0000, 0b0010);
  auto* expr = MakeBinary(f.arena, TokenKind::kGtGt, MakeId(f.arena, "v"),
                          MakeId(f.arena, "sa"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

// §11.4.10: an x or z in the shift amount makes the result unknown. This holds
// for every shift operator, so the arithmetic left shift completes the set
// already exercised for <<, >>, and >>>.
TEST(EvalOpXZ, ArithLeftShiftXAmount) {
  SimFixture f;
  MakeVar(f, "v", 4, 0b1100);
  MakeVar4(f, "sa", 4, 0b0000, 0b0010);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtLtLt, MakeId(f.arena, "v"),
                          MakeId(f.arena, "sa"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalRightShiftXOperand) {
  SimFixture f;

  MakeVar4(f, "so", 4, 0b1000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kGtGt, MakeId(f.arena, "so"),
                          MakeInt(f.arena, 1));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.words[0].aval & 0xFu, 0b0100u);
  EXPECT_EQ(result.words[0].bval & 0xFu, 0b0010u);
}

TEST(OperatorSim, ShiftResultSignednessFromLhs) {
  SimFixture f;

  MakeSignedVarAdv(f, "s", 8, 0x0F);
  MakeVar(f, "amt", 4, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtLt, MakeId(f.arena, "s"),
                          MakeId(f.arena, "amt"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);

  MakeVar(f, "u", 8, 0x0F);
  MakeSignedVarAdv(f, "samt", 4, 2);
  auto* expr2 = MakeBinary(f.arena, TokenKind::kLtLt, MakeId(f.arena, "u"),
                           MakeId(f.arena, "samt"));
  auto result2 = EvalExpr(expr2, f.ctx, f.arena);
  EXPECT_FALSE(result2.is_signed);
}

TEST(OperatorSim, AllShiftOpsPreserveLhsSignedness) {
  SimFixture f;
  MakeSignedVarAdv(f, "s", 8, 0x0F);
  MakeVar(f, "amt", 4, 1);

  TokenKind ops[] = {TokenKind::kLtLt, TokenKind::kGtGt, TokenKind::kLtLtLt,
                     TokenKind::kGtGtGt};
  for (auto op : ops) {
    auto* expr =
        MakeBinary(f.arena, op, MakeId(f.arena, "s"), MakeId(f.arena, "amt"));
    auto result = EvalExpr(expr, f.ctx, f.arena);
    EXPECT_TRUE(result.is_signed);
  }
}

// §11.4.10: the shift amount is always treated as an unsigned number. A signed
// right operand whose sign bit is set is applied as its (large) unsigned
// magnitude, never as a negative count. The 5-bit signed amount 0b10000 here is
// 16 when read unsigned, shifting the 32-bit all-ones operand down to its upper
// half rather than doing anything sign-driven.
TEST(OperatorSim, ShiftAmountTreatedAsUnsigned) {
  SimFixture f;
  MakeVar(f, "u", 32, 0xFFFFFFFFu);
  MakeSignedVarAdv(f, "amt", 5, 0b10000);
  auto* expr = MakeBinary(f.arena, TokenKind::kGtGt, MakeId(f.arena, "u"),
                          MakeId(f.arena, "amt"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFFFFFFFFull, 0xFFFFu);
}

TEST(OperatorSim, ShiftByZero) {
  SimFixture f;
  MakeVar(f, "v", 8, 0xAB);
  TokenKind ops[] = {TokenKind::kLtLt, TokenKind::kGtGt, TokenKind::kLtLtLt,
                     TokenKind::kGtGtGt};
  for (auto op : ops) {
    auto* expr =
        MakeBinary(f.arena, op, MakeId(f.arena, "v"), MakeInt(f.arena, 0));
    auto result = EvalExpr(expr, f.ctx, f.arena);
    EXPECT_EQ(result.ToUint64() & 0xFFu, 0xABu);
  }
}

TEST(OperatorSim, ShiftByMoreThanWidth) {
  SimFixture f;
  MakeVar(f, "v", 4, 0b1111);
  auto* expr_l = MakeBinary(f.arena, TokenKind::kLtLt, MakeId(f.arena, "v"),
                            MakeInt(f.arena, 5));
  EXPECT_EQ(EvalExpr(expr_l, f.ctx, f.arena).ToUint64() & 0xFu, 0u);

  auto* expr_r = MakeBinary(f.arena, TokenKind::kGtGt, MakeId(f.arena, "v"),
                            MakeInt(f.arena, 5));
  EXPECT_EQ(EvalExpr(expr_r, f.ctx, f.arena).ToUint64() & 0xFu, 0u);
}

// §11.4.10: the arithmetic right shift sign-fills the vacated high bits when
// the result type is signed. Signedness is a property of the operand's
// declaration, so this drives a real `logic signed` variable through the full
// pipeline: the lowerer propagates the declared signedness onto the runtime
// value and the runtime shift reads it to choose sign-fill over zero-fill.
// 4'b1000 is -8, and an arithmetic right shift by 1 yields 4'b1100 (-4) rather
// than the 4'b0100 a zero-fill would produce, so the fill source is observed
// from source syntax.
TEST(OperatorSim, ArithRightShiftSignedDeclSignFillsFromSource) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic signed [3:0] s;\n"
      "  logic signed [3:0] r;\n"
      "  initial begin\n"
      "    s = 4'b1000;\n"
      "    r = s >>> 1;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64() & 0xFu, 0b1100u);
}

// §11.4.10: an x or z in the shift amount forces an unknown result. The
// synthetic EvalOpXZ cases above hand-build a z amount (aval=0, bval=1); this
// drives a true-x amount (the 4'bx literal lowers to aval=1, bval=1) through
// the full pipeline from real source, so the HasUnknownBits gate is observed
// acting on an amount produced exactly the way a design would produce one.
TEST(OperatorSim, UnknownShiftAmountFromSourceYieldsUnknown) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  logic [3:0] amt;\n"
      "  initial begin\n"
      "    amt = 4'bx;\n"
      "    r = 8'hFF >> amt;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_NE(r->value.words[0].bval & 0xFFu, 0u);
}

TEST(AlwaysCombBasicSim, AlwaysCombBitSelect) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'b0000_0100;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = a >> 2;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(AlwaysCombBasicSim, AlwaysCombUpperPartSelect) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = (a >> 4) & 8'h0F;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

TEST(AlwaysCombBasicSim, AlwaysCombShift) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, result;\n"
      "  initial a = 8'b0000_0011;\n"
      "  always_comb begin\n"
      "    result = a << 4;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x30u);
}

TEST(BlockingAssignSim, BlockingAssignShiftOps) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] r_shl, r_shr;\n"
      "  initial begin\n"
      "    a = 8'h0F;\n"
      "    r_shl = a << 2;\n"
      "    r_shr = a >> 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* shl = f.ctx.FindVariable("r_shl");
  auto* shr = f.ctx.FindVariable("r_shr");
  ASSERT_NE(shl, nullptr);
  ASSERT_NE(shr, nullptr);

  EXPECT_EQ(shl->value.ToUint64(), 0x3Cu);

  EXPECT_EQ(shr->value.ToUint64(), 0x03u);
}

// §11.4.10 (printed page 284) has every shift move the whole left operand by
// the count and fill the vacated positions with zeros, so a 96-bit operand
// shifted right by 64 reads its top word at the bottom. The runtime moved
// words[0] alone by the count taken on a 64-bit machine word, where a count
// of 64 is undefined and moved nothing on x86, so P >> 64 read
// 0x89ABCDEF00112233 with the top word cleared.
constexpr const char* kWideShiftHeader =
    "module t;\n"
    "  localparam logic [95:0] P = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
    "  logic [95:0] r;\n";

TEST(WideShiftSim, LogicalRightShiftByAWholeWordReadsTheTopWord) {
  SimFixture f;
  auto* r = RunAndFindVar(std::string(kWideShiftHeader) +
                              "  initial r = P >> 64;\n"
                              "endmodule\n",
                          f, "r");
  ASSERT_NE(r, nullptr);
  ASSERT_EQ(r->value.nwords, 2u);
  EXPECT_EQ(r->value.words[0].aval, 0x01234567u);
  EXPECT_EQ(r->value.words[1].aval, 0u);
  EXPECT_FALSE(f.has_errors);
}

// A count of 70 is one word and six bits: 0x01234567 >> 6 is 0x48D15. The
// defect read 0x0226AF37BC004488, words[0] moved by six alone.
TEST(WideShiftSim, LogicalRightShiftByAWordAndBitsCrossesTheWord) {
  SimFixture f;
  auto* r = RunAndFindVar(std::string(kWideShiftHeader) +
                              "  initial r = P >> 70;\n"
                              "endmodule\n",
                          f, "r");
  ASSERT_NE(r, nullptr);
  ASSERT_EQ(r->value.nwords, 2u);
  EXPECT_EQ(r->value.words[0].aval, 0x48D15u);
  EXPECT_EQ(r->value.words[1].aval, 0u);
}

// A count under 64 still draws the top word's bits down into the low word:
// P >> 32 is 0x0123456789ABCDEF, where the defect read 0x89ABCDEF.
TEST(WideShiftSim, LogicalRightShiftWithinAWordDrawsFromTheWordAbove) {
  SimFixture f;
  auto* r = RunAndFindVar(std::string(kWideShiftHeader) +
                              "  initial r = P >> 32;\n"
                              "endmodule\n",
                          f, "r");
  ASSERT_NE(r, nullptr);
  ASSERT_EQ(r->value.nwords, 2u);
  EXPECT_EQ(r->value.words[0].aval, 0x0123456789ABCDEFull);
  EXPECT_EQ(r->value.words[1].aval, 0u);
}

// P << 64 carries the low word's low 32 bits into bits 95:64 and leaves the
// low word clear. The defect left words[0] as P's and words[1] at 0.
TEST(WideShiftSim, LeftShiftByAWholeWordFillsTheTopWord) {
  SimFixture f;
  auto* r = RunAndFindVar(std::string(kWideShiftHeader) +
                              "  initial r = P << 64;\n"
                              "endmodule\n",
                          f, "r");
  ASSERT_NE(r, nullptr);
  ASSERT_EQ(r->value.nwords, 2u);
  EXPECT_EQ(r->value.words[0].aval, 0u);
  EXPECT_EQ(r->value.words[1].aval, 0x00112233u);
}

// P << 70 puts 0x00112233 << 6, 0x04488CC0, in bits 95:64; the defect read
// 0x6AF37BC004488CC0 in words[0] and nothing above.
TEST(WideShiftSim, LeftShiftByAWordAndBitsCrossesTheWord) {
  SimFixture f;
  auto* r = RunAndFindVar(std::string(kWideShiftHeader) +
                              "  initial r = P << 70;\n"
                              "endmodule\n",
                          f, "r");
  ASSERT_NE(r, nullptr);
  ASSERT_EQ(r->value.nwords, 2u);
  EXPECT_EQ(r->value.words[0].aval, 0u);
  EXPECT_EQ(r->value.words[1].aval, 0x04488CC0u);
}

// P << 32 keeps the low word's carry: words[1] takes P[63:32], 0x89ABCDEF,
// which the defect dropped while it got words[0] right.
TEST(WideShiftSim, LeftShiftWithinAWordCarriesIntoTheWordAbove) {
  SimFixture f;
  auto* r = RunAndFindVar(std::string(kWideShiftHeader) +
                              "  initial r = P << 32;\n"
                              "endmodule\n",
                          f, "r");
  ASSERT_NE(r, nullptr);
  ASSERT_EQ(r->value.nwords, 2u);
  EXPECT_EQ(r->value.words[0].aval, 0x0011223300000000ull);
  EXPECT_EQ(r->value.words[1].aval, 0x89ABCDEFu);
}

// §11.4.10: a count of the operand's width or more leaves no bit of it. The
// defect took 96 as 32 and read 0x89ABCDEF, and 100 as 36.
TEST(WideShiftSim, ShiftByTheWidthOrMoreIsAllZeros) {
  SimFixture f;
  auto* r = RunAndFindVar(std::string(kWideShiftHeader) +
                              "  logic [95:0] s, u;\n"
                              "  initial begin\n"
                              "    r = P >> 96;\n"
                              "    s = P >> 100;\n"
                              "    u = P << 100;\n"
                              "  end\n"
                              "endmodule\n",
                          f, "r");
  ASSERT_NE(r, nullptr);
  auto* s = f.ctx.FindVariable("s");
  auto* u = f.ctx.FindVariable("u");
  ASSERT_NE(s, nullptr);
  ASSERT_NE(u, nullptr);
  for (auto* v : {r, s, u}) {
    ASSERT_EQ(v->value.nwords, 2u);
    EXPECT_EQ(v->value.words[0].aval, 0u);
    EXPECT_EQ(v->value.words[1].aval, 0u);
  }
}

// A shift by zero keeps every word; the defect rebuilt the result from the
// low word alone and so cleared words[1].
TEST(WideShiftSim, ShiftByZeroKeepsEveryWord) {
  SimFixture f;
  auto* r = RunAndFindVar(std::string(kWideShiftHeader) +
                              "  initial r = P >> 0;\n"
                              "endmodule\n",
                          f, "r");
  ASSERT_NE(r, nullptr);
  ASSERT_EQ(r->value.nwords, 2u);
  EXPECT_EQ(r->value.words[0].aval, 0x89ABCDEF00112233ull);
  EXPECT_EQ(r->value.words[1].aval, 0x01234567u);
}

// §11.4.10: >>> fills the vacated positions with the sign bit when the result
// is signed. N is -2^80 as a 96-bit signed value; N >>> 70 is -2^10, ones
// down to bit 10 in both words. The defect zero-filled a signed operand of 64
// bits or more and read 0 in both words.
TEST(WideShiftSim, ArithmeticRightShiftSignFillsAcrossWords) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  localparam logic signed [95:0] N = "
      "96'hFFFF_0000_0000_0000_0000_0000;\n"
      "  logic signed [95:0] r;\n"
      "  initial r = N >>> 70;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  ASSERT_EQ(r->value.nwords, 2u);
  EXPECT_EQ(r->value.words[0].aval, 0xFFFFFFFFFFFFFC00ull);
  EXPECT_EQ(r->value.words[1].aval, 0xFFFFFFFFu);
  EXPECT_EQ(r->value.words[0].bval, 0u);
  EXPECT_EQ(r->value.words[1].bval, 0u);
}

// A signed operand shifted by its width or more is the sign bit everywhere,
// inside the width and not above it.
TEST(WideShiftSim, ArithmeticRightShiftByTheWidthOrMoreIsAllSignBits) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  localparam logic signed [95:0] N = "
      "96'hFFFF_0000_0000_0000_0000_0000;\n"
      "  logic signed [95:0] r, s;\n"
      "  initial begin\n"
      "    r = N >>> 96;\n"
      "    s = N >>> 200;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  auto* s = f.ctx.FindVariable("s");
  ASSERT_NE(s, nullptr);
  for (auto* v : {r, s}) {
    ASSERT_EQ(v->value.nwords, 2u);
    EXPECT_EQ(v->value.words[0].aval, 0xFFFFFFFFFFFFFFFFull);
    EXPECT_EQ(v->value.words[1].aval, 0xFFFFFFFFu);
  }
}

// The logical >> on the same bits zero-fills whatever the operand's sign:
// N >> 70 is 0x3FFFC00.
TEST(WideShiftSim, LogicalRightShiftOfASignedOperandZeroFills) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  localparam logic signed [95:0] N = "
      "96'hFFFF_0000_0000_0000_0000_0000;\n"
      "  logic [95:0] r;\n"
      "  initial r = N >> 70;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  ASSERT_EQ(r->value.nwords, 2u);
  EXPECT_EQ(r->value.words[0].aval, 0x3FFFC00u);
  EXPECT_EQ(r->value.words[1].aval, 0u);
}

// An x or z bit of the operand travels with the shift on both planes: 4'bx01z
// deposited at q[95:92] and shifted down by 92 reads x01z at r[3:0], aval
// 0b1010 and bval 0b1001. The defect read 0 on both planes.
TEST(WideShiftSim, LogicalRightShiftCarriesUnknownBitsDownAcrossWords) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [95:0] q, r;\n"
      "  initial begin\n"
      "    q = 96'h0;\n"
      "    q[95:92] = 4'bx01z;\n"
      "    r = q >> 92;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  ASSERT_EQ(r->value.nwords, 2u);
  EXPECT_EQ(r->value.words[0].aval, 0b1010u);
  EXPECT_EQ(r->value.words[0].bval, 0b1001u);
  EXPECT_EQ(r->value.words[1].aval, 0u);
  EXPECT_EQ(r->value.words[1].bval, 0u);
}

// §11.4.10 treats the count as unsigned, so a count with a bit above its low
// 64 is beyond any width and answers zeros. Read through the count's low word
// alone it is 0 and left P untouched.
TEST(WideShiftSim, ACountAboveSixtyFourBitsIsBeyondTheWidth) {
  SimFixture f;
  auto* r = RunAndFindVar(std::string(kWideShiftHeader) +
                              "  localparam logic [127:0] C = "
                              "128'h0000_0000_0000_0001_0000_0000_0000_0000;\n"
                              "  initial r = P >> C;\n"
                              "endmodule\n",
                          f, "r");
  ASSERT_NE(r, nullptr);
  ASSERT_EQ(r->value.nwords, 2u);
  EXPECT_EQ(r->value.words[0].aval, 0u);
  EXPECT_EQ(r->value.words[1].aval, 0u);
}

}  // namespace
