#include <cstring>

#include "builders_ast.h"
#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(BitwiseTruthTable, Logic4WordNot) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x_val = {0, 1};

  auto r1 = Logic4Not(zero);
  EXPECT_EQ(r1.aval, ~uint64_t(0));
  EXPECT_EQ(r1.bval, 0);

  auto r2 = Logic4Not(one);
  EXPECT_EQ(r2.aval, ~uint64_t(1));
  EXPECT_EQ(r2.bval, 0);

  auto r3 = Logic4Not(x_val);
  EXPECT_NE(r3.bval, 0);
}

TEST(BitwiseEval, BinaryXnorBasic) {
  SimFixture f;

  auto* a = f.ctx.CreateVariable("xa", 4);
  a->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* b = f.ctx.CreateVariable("xb", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b1010);

  auto* expr = MakeBinary(f.arena, TokenKind::kTildeCaret,
                          MakeId(f.arena, "xa"), MakeId(f.arena, "xb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.ToUint64(), 0b1001u);
}

TEST(BitwiseEval, BinaryXnorWithX) {
  SimFixture f;

  auto* a = f.ctx.CreateVariable("za", 4);
  a->value = MakeLogic4Vec(f.arena, 4);
  a->value.words[0].aval = 0b1100;  // bit2 = x = (aval=1, bval=1)
  a->value.words[0].bval = 0b0100;

  auto* b = f.ctx.CreateVariable("zb", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b1010);

  auto* expr = MakeBinary(f.arena, TokenKind::kTildeCaret,
                          MakeId(f.arena, "za"), MakeId(f.arena, "zb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.words[0].aval, 0b1101u);  // bit2 = x = (aval=1, bval=1)
  EXPECT_EQ(result.words[0].bval, 0b0100u);
}

TEST(OperatorSim, UnaryBitwiseNot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'h0F; x = ~x; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64() & 0xFFu, 0xF0u);
}

TEST(OperatorSim, BinaryBitwiseAnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hF0 & 8'h3C;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x30u);
}

TEST(OperatorSim, BinaryBitwiseOr) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hF0 | 8'h0F;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(OperatorSim, BinaryBitwiseXor) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hFF ^ 8'h0F;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xF0u);
}

TEST(OperatorSim, BinaryBitwiseXnor) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hFF ^~ 8'h0F;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(BitwiseTruthTable, Logic4WordNotWithZ) {
  Logic4Word z_val = {1, 1};

  auto r = Logic4Not(z_val);
  EXPECT_NE(r.bval, 0u);
}

TEST(BitwiseEval, BinaryAndBothSignedYieldsSigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "sa", 8, 0xFF);
  MakeSignedVarAdv(f, "sb", 8, 0x0F);
  auto* expr = MakeBinary(f.arena, TokenKind::kAmp, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x0Fu);
  EXPECT_TRUE(result.is_signed);
}

TEST(BitwiseEval, BinaryAndMixedSignYieldsUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "sa", 8, 0xFF);
  MakeVar(f, "ub", 8, 0x0F);
  auto* expr = MakeBinary(f.arena, TokenKind::kAmp, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "ub"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x0Fu);
  EXPECT_FALSE(result.is_signed);
}

TEST(BitwiseEval, BinaryOrBothSignedYieldsSigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "sa", 8, 0xF0);
  MakeSignedVarAdv(f, "sb", 8, 0x0F);
  auto* expr = MakeBinary(f.arena, TokenKind::kPipe, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
  EXPECT_TRUE(result.is_signed);
}

TEST(BitwiseEval, BinaryOrMixedSignYieldsUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "sa", 8, 0xF0);
  MakeVar(f, "ub", 8, 0x0F);
  auto* expr = MakeBinary(f.arena, TokenKind::kPipe, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "ub"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
  EXPECT_FALSE(result.is_signed);
}

TEST(BitwiseEval, BinaryXorBothSignedYieldsSigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "sa", 8, 0xFF);
  MakeSignedVarAdv(f, "sb", 8, 0x0F);
  auto* expr = MakeBinary(f.arena, TokenKind::kCaret, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xF0u);
  EXPECT_TRUE(result.is_signed);
}

TEST(BitwiseEval, BinaryXorMixedSignYieldsUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "sa", 8, 0xFF);
  MakeVar(f, "ub", 8, 0x0F);
  auto* expr = MakeBinary(f.arena, TokenKind::kCaret, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "ub"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xF0u);
  EXPECT_FALSE(result.is_signed);
}

TEST(BitwiseEval, BinaryXnorBothSignedYieldsSigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "sa", 4, 0b1100);
  MakeSignedVarAdv(f, "sb", 4, 0b1010);
  auto* expr = MakeBinary(f.arena, TokenKind::kTildeCaret,
                          MakeId(f.arena, "sa"), MakeId(f.arena, "sb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0b1001u);
  EXPECT_TRUE(result.is_signed);
}

TEST(BitwiseEval, BinaryXnorMixedSignYieldsUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "sa", 4, 0b1100);
  MakeVar(f, "ub", 4, 0b1010);
  auto* expr = MakeBinary(f.arena, TokenKind::kTildeCaret,
                          MakeId(f.arena, "sa"), MakeId(f.arena, "ub"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0b1001u);
  EXPECT_FALSE(result.is_signed);
}

// §11.4.8: for the unary bitwise negation operator, if the operand is signed
// the result is signed. Signedness is a property of the operand's declaration,
// so this drives a real `logic signed` operand through the full pipeline: the
// negation of the 4-bit value 4'b0001 is 4'b1110, whose result is signed, so
// widening it to the 8-bit assignment target sign-extends the top bit and
// yields 8'hFE. Were the result unsigned, the widening would zero-extend to
// 8'h0E, so the signed result is observed from source syntax.
TEST(OperatorSim, UnaryBitwiseNotSignedOperandResultSignExtendsFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [3:0] a;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    a = 4'b0001;\n"
      "    y = ~a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64() & 0xFFu, 0xFEu);
}

// §11.4.8: if the operand of the unary bitwise negation operator is unsigned,
// the result is unsigned. Same real-source construction as the signed case but
// with a plain (unsigned) `logic` operand: ~4'b0001 = 4'b1110, an unsigned
// result, so widening to the 8-bit target zero-extends to 8'h0E rather than the
// 8'hFE a signed result would sign-extend to.
TEST(OperatorSim, UnaryBitwiseNotUnsignedOperandResultZeroExtendsFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    a = 4'b0001;\n"
      "    y = ~a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64() & 0xFFu, 0x0Eu);
}

// §11.4.8: for a binary bitwise operator whose operands are of unequal bit
// length, the smaller operand is extended to the size of the larger before the
// bit-by-bit combination, and when both operands are signed that extension is a
// sign-extension. Signedness is a property of each operand's declaration, so
// this drives real `logic signed` declarations through the full pipeline rather
// than hand-building a signed carrier. The narrow operand 4'b1111 sign-extends
// to 8'hFF, so OR-ing with zero yields 8'hFF -- a zero-extension would instead
// have produced 8'h0F, so the sign-fill is observed from source syntax.
TEST(OperatorSim, BinaryBitwiseBothSignedSignExtendsSmallerFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [3:0] narrow;\n"
      "  logic signed [7:0] wide;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    narrow = 4'b1111;\n"
      "    wide = 8'h00;\n"
      "    y = narrow | wide;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64() & 0xFFu, 0xFFu);
}

// §11.4.8: if one or both operands of a binary bitwise operator are unsigned,
// the operation is unsigned and the smaller operand is zero-extended -- even
// when the smaller operand is itself declared signed. This mixed-signedness
// case is where the sign- vs zero-extension decision diverges: the unsigned
// `wide` operand makes the whole operation unsigned, so the signed narrow value
// 4'b1111 must be zero-extended (not sign-extended). OR-ing with zero then
// yields 8'h0F; had the narrow operand's own sign governed the fill the result
// would have been 8'hFF, so this observes the "one operand unsigned" rule.
TEST(OperatorSim, BinaryBitwiseMixedSignZeroExtendsSmallerFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [3:0] narrow;\n"
      "  logic [7:0] wide;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    narrow = 4'b1111;\n"
      "    wide = 8'h00;\n"
      "    y = narrow | wide;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64() & 0xFFu, 0x0Fu);
}

// §11.4.8: two unsigned operands of unequal width also zero-extend the smaller
// operand, so a set narrow field never leaks 1s into the high bits. Driven from
// plain (unsigned) `logic` declarations through the full pipeline.
TEST(OperatorSim, BinaryBitwiseBothUnsignedZeroExtendsSmallerFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  logic [7:0] wide;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    narrow = 4'b1111;\n"
      "    wide = 8'h00;\n"
      "    y = narrow | wide;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64() & 0xFFu, 0x0Fu);
}

TEST(BitwiseEval, UnaryNotMasksTopWord) {
  SimFixture f;
  MakeVar(f, "v", 4, 0x0);
  auto* expr = MakeUnary(f.arena, TokenKind::kTilde, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);

  EXPECT_EQ(result.ToUint64(), 0xFu);
  EXPECT_EQ(result.words[0].bval, 0u);
}

constexpr Logic4Word kFour[4] = {
    {0, 0},
    {1, 0},
    {0, 1},
    {1, 1},
};
constexpr Logic4Word kOut0 = {0, 0};
constexpr Logic4Word kOut1 = {1, 0};
constexpr Logic4Word kOutX = {1, 1};  // canonical Convention A: x = (1, 1)

TEST(BitwiseTruthTable, BinaryAndAllCells) {
  const Logic4Word kExpected[4][4] = {
      {kOut0, kOut0, kOut0, kOut0},
      {kOut0, kOut1, kOutX, kOutX},
      {kOut0, kOutX, kOutX, kOutX},
      {kOut0, kOutX, kOutX, kOutX},
  };
  for (int i = 0; i < 4; ++i) {
    for (int j = 0; j < 4; ++j) {
      auto r = Logic4And(kFour[i], kFour[j]);
      EXPECT_EQ(r.aval & 1u, kExpected[i][j].aval)
          << "row=" << i << " col=" << j;
      EXPECT_EQ(r.bval & 1u, kExpected[i][j].bval)
          << "row=" << i << " col=" << j;
    }
  }
}

TEST(BitwiseTruthTable, BinaryOrAllCells) {
  const Logic4Word kExpected[4][4] = {
      {kOut0, kOut1, kOutX, kOutX},
      {kOut1, kOut1, kOut1, kOut1},
      {kOutX, kOut1, kOutX, kOutX},
      {kOutX, kOut1, kOutX, kOutX},
  };
  for (int i = 0; i < 4; ++i) {
    for (int j = 0; j < 4; ++j) {
      auto r = Logic4Or(kFour[i], kFour[j]);
      EXPECT_EQ(r.aval & 1u, kExpected[i][j].aval)
          << "row=" << i << " col=" << j;
      EXPECT_EQ(r.bval & 1u, kExpected[i][j].bval)
          << "row=" << i << " col=" << j;
    }
  }
}

TEST(BitwiseTruthTable, BinaryXorAllCells) {
  const Logic4Word kExpected[4][4] = {
      {kOut0, kOut1, kOutX, kOutX},
      {kOut1, kOut0, kOutX, kOutX},
      {kOutX, kOutX, kOutX, kOutX},
      {kOutX, kOutX, kOutX, kOutX},
  };
  for (int i = 0; i < 4; ++i) {
    for (int j = 0; j < 4; ++j) {
      auto r = Logic4Xor(kFour[i], kFour[j]);
      EXPECT_EQ(r.aval & 1u, kExpected[i][j].aval)
          << "row=" << i << " col=" << j;
      EXPECT_EQ(r.bval & 1u, kExpected[i][j].bval)
          << "row=" << i << " col=" << j;
    }
  }
}

TEST(BitwiseTruthTable, BinaryXnorAllCells) {
  const Logic4Word kExpected[4][4] = {
      {kOut1, kOut0, kOutX, kOutX},
      {kOut0, kOut1, kOutX, kOutX},
      {kOutX, kOutX, kOutX, kOutX},
      {kOutX, kOutX, kOutX, kOutX},
  };
  for (int i = 0; i < 4; ++i) {
    for (int j = 0; j < 4; ++j) {
      auto r = Logic4Not(Logic4Xor(kFour[i], kFour[j]));
      EXPECT_EQ(r.aval & 1u, kExpected[i][j].aval)
          << "row=" << i << " col=" << j;
      EXPECT_EQ(r.bval & 1u, kExpected[i][j].bval)
          << "row=" << i << " col=" << j;
    }
  }
}

TEST(BitwiseEval, BinaryAndBothUnsignedYieldsUnsigned) {
  SimFixture f;
  MakeVar(f, "ua", 8, 0xFF);
  MakeVar(f, "ub", 8, 0x0F);
  auto* expr = MakeBinary(f.arena, TokenKind::kAmp, MakeId(f.arena, "ua"),
                          MakeId(f.arena, "ub"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x0Fu);
  EXPECT_FALSE(result.is_signed);
}

TEST(BitwiseEval, BinaryOrBothUnsignedYieldsUnsigned) {
  SimFixture f;
  MakeVar(f, "ua", 8, 0xF0);
  MakeVar(f, "ub", 8, 0x0F);
  auto* expr = MakeBinary(f.arena, TokenKind::kPipe, MakeId(f.arena, "ua"),
                          MakeId(f.arena, "ub"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
  EXPECT_FALSE(result.is_signed);
}

TEST(BitwiseEval, BinaryXorBothUnsignedYieldsUnsigned) {
  SimFixture f;
  MakeVar(f, "ua", 8, 0xFF);
  MakeVar(f, "ub", 8, 0x0F);
  auto* expr = MakeBinary(f.arena, TokenKind::kCaret, MakeId(f.arena, "ua"),
                          MakeId(f.arena, "ub"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xF0u);
  EXPECT_FALSE(result.is_signed);
}

TEST(BitwiseEval, BinaryXnorBothUnsignedYieldsUnsigned) {
  SimFixture f;
  MakeVar(f, "ua", 4, 0b1100);
  MakeVar(f, "ub", 4, 0b1010);
  auto* expr = MakeBinary(f.arena, TokenKind::kTildeCaret,
                          MakeId(f.arena, "ua"), MakeId(f.arena, "ub"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0b1001u);
  EXPECT_FALSE(result.is_signed);
}

}  // namespace
