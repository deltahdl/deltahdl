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

TEST(ShiftOperatorSim, ShiftLeftOperandTakesTheContextsWidth) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  logic [15:0] w, w2, w3; logic [3:0] a = 4'b1111; int r1, r2;\n"
      "  initial begin\n"
      "    w = 8'd1 << 8; r1 = a << 4; w3 = (8'd1 << 8) + 0;\n"
      "    w2 = {8'd1 << 8}; r2 = {a << 4};\n"
      "    $display(\"%0d %0d %0d %0d %0d\", w, r1, w3, w2, r2);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "256 240 256 0 0\n");
}

}  // namespace
