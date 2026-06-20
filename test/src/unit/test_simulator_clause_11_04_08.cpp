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

TEST(BitwiseTruthTable, Logic4WordAnd) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x_val = {0, 1};

  struct Case {
    Logic4Word a;
    Logic4Word b;
    uint64_t exp_aval;
    uint64_t exp_bval;
    const char* label;
  };
  const Case kCases[] = {
      {one, one, 1, 0, "1 & 1 = 1"},
      {one, zero, 0, 0, "1 & 0 = 0"},
      {zero, x_val, 0, 0, "0 & x = 0"},
  };
  for (const auto& c : kCases) {
    auto r = Logic4And(c.a, c.b);
    EXPECT_EQ(r.aval, c.exp_aval) << c.label;
    EXPECT_EQ(r.bval, c.exp_bval) << c.label;
  }

  auto r4 = Logic4And(one, x_val);
  EXPECT_NE(r4.bval, 0);
}

TEST(BitwiseTruthTable, Logic4WordOr) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x_val = {0, 1};

  struct Case {
    Logic4Word a;
    Logic4Word b;
    uint64_t exp_aval;
    uint64_t exp_bval;
    const char* label;
  };
  const Case kCases[] = {
      {zero, zero, 0, 0, "0 | 0 = 0"},
      {one, zero, 1, 0, "1 | 0 = 1"},
      {one, x_val, 1, 0, "1 | x = 1"},
  };
  for (const auto& c : kCases) {
    auto r = Logic4Or(c.a, c.b);
    EXPECT_EQ(r.aval, c.exp_aval) << c.label;
    EXPECT_EQ(r.bval, c.exp_bval) << c.label;
  }
}

TEST(BitwiseTruthTable, Logic4WordXor) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};

  auto r1 = Logic4Xor(one, zero);
  EXPECT_EQ(r1.aval, 1);
  EXPECT_EQ(r1.bval, 0);

  auto r2 = Logic4Xor(one, one);
  EXPECT_EQ(r2.aval, 0);
  EXPECT_EQ(r2.bval, 0);
}

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
  a->value.words[0].aval = 0b1000;
  a->value.words[0].bval = 0b0100;

  auto* b = f.ctx.CreateVariable("zb", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b1010);

  auto* expr = MakeBinary(f.arena, TokenKind::kTildeCaret,
                          MakeId(f.arena, "za"), MakeId(f.arena, "zb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.words[0].aval, 0b1001u);
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

TEST(BitwiseTruthTable, Logic4WordAndWithZ) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word z_val = {1, 1};

  auto r1 = Logic4And(zero, z_val);
  EXPECT_EQ(r1.aval, 0u);
  EXPECT_EQ(r1.bval, 0u);

  auto r2 = Logic4And(one, z_val);
  EXPECT_NE(r2.bval, 0u);

  auto r3 = Logic4And(z_val, z_val);
  EXPECT_NE(r3.bval, 0u);
}

TEST(BitwiseTruthTable, Logic4WordOrWithZ) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word z_val = {1, 1};

  auto r1 = Logic4Or(one, z_val);
  EXPECT_EQ(r1.aval, 1u);
  EXPECT_EQ(r1.bval, 0u);

  auto r2 = Logic4Or(zero, z_val);
  EXPECT_NE(r2.bval, 0u);

  auto r3 = Logic4Or(z_val, z_val);
  EXPECT_NE(r3.bval, 0u);
}

TEST(BitwiseTruthTable, Logic4WordXorWithZ) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word z_val = {1, 1};

  auto r1 = Logic4Xor(zero, z_val);
  EXPECT_NE(r1.bval, 0u);

  auto r2 = Logic4Xor(one, z_val);
  EXPECT_NE(r2.bval, 0u);
}

TEST(BitwiseTruthTable, Logic4WordNotWithZ) {
  Logic4Word z_val = {1, 1};

  auto r = Logic4Not(z_val);
  EXPECT_NE(r.bval, 0u);
}

TEST(BitwiseTruthTable, Logic4WordXnor) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x_val = {0, 1};

  auto r1 = Logic4Not(Logic4Xor(zero, zero));
  EXPECT_EQ(r1.aval & 1u, 1u);
  EXPECT_EQ(r1.bval & 1u, 0u);

  auto r2 = Logic4Not(Logic4Xor(zero, one));
  EXPECT_EQ(r2.aval & 1u, 0u);
  EXPECT_EQ(r2.bval & 1u, 0u);

  auto r3 = Logic4Not(Logic4Xor(one, zero));
  EXPECT_EQ(r3.aval & 1u, 0u);
  EXPECT_EQ(r3.bval & 1u, 0u);

  auto r4 = Logic4Not(Logic4Xor(one, one));
  EXPECT_EQ(r4.aval & 1u, 1u);
  EXPECT_EQ(r4.bval & 1u, 0u);

  auto r5 = Logic4Not(Logic4Xor(x_val, zero));
  EXPECT_NE(r5.bval & 1u, 0u);
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

TEST(BitwiseEval, UnaryNotSignedYieldsSigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "sv", 8, 0x0F);
  auto* expr = MakeUnary(f.arena, TokenKind::kTilde, MakeId(f.arena, "sv"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFFu, 0xF0u);
  EXPECT_TRUE(result.is_signed);
}

TEST(BitwiseEval, UnaryNotUnsignedYieldsUnsigned) {
  SimFixture f;
  MakeVar(f, "uv", 8, 0x0F);
  auto* expr = MakeUnary(f.arena, TokenKind::kTilde, MakeId(f.arena, "uv"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFFu, 0xF0u);
  EXPECT_FALSE(result.is_signed);
}

TEST(BitwiseEval, UnequalWidthZeroExtends) {
  SimFixture f;

  MakeVar(f, "narrow", 4, 0xF);
  MakeVar(f, "wide", 8, 0x00);
  auto* expr = MakeBinary(f.arena, TokenKind::kPipe, MakeId(f.arena, "narrow"),
                          MakeId(f.arena, "wide"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);

  EXPECT_EQ(result.ToUint64(), 0x0Fu);
}

TEST(BitwiseEval, UnequalWidthSignExtends) {
  SimFixture f;

  MakeSignedVarAdv(f, "narrow", 4, 0xF);
  MakeSignedVarAdv(f, "wide", 8, 0x00);
  auto* expr = MakeBinary(f.arena, TokenKind::kPipe, MakeId(f.arena, "narrow"),
                          MakeId(f.arena, "wide"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
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
constexpr Logic4Word kOutX = {0, 1};

TEST(BitwiseTruthTable, BinaryAndAllCells) {
  const Logic4Word expected[4][4] = {
      {kOut0, kOut0, kOut0, kOut0},
      {kOut0, kOut1, kOutX, kOutX},
      {kOut0, kOutX, kOutX, kOutX},
      {kOut0, kOutX, kOutX, kOutX},
  };
  for (int i = 0; i < 4; ++i) {
    for (int j = 0; j < 4; ++j) {
      auto r = Logic4And(kFour[i], kFour[j]);
      EXPECT_EQ(r.aval & 1u, expected[i][j].aval)
          << "row=" << i << " col=" << j;
      EXPECT_EQ(r.bval & 1u, expected[i][j].bval)
          << "row=" << i << " col=" << j;
    }
  }
}

TEST(BitwiseTruthTable, BinaryOrAllCells) {
  const Logic4Word expected[4][4] = {
      {kOut0, kOut1, kOutX, kOutX},
      {kOut1, kOut1, kOut1, kOut1},
      {kOutX, kOut1, kOutX, kOutX},
      {kOutX, kOut1, kOutX, kOutX},
  };
  for (int i = 0; i < 4; ++i) {
    for (int j = 0; j < 4; ++j) {
      auto r = Logic4Or(kFour[i], kFour[j]);
      EXPECT_EQ(r.aval & 1u, expected[i][j].aval)
          << "row=" << i << " col=" << j;
      EXPECT_EQ(r.bval & 1u, expected[i][j].bval)
          << "row=" << i << " col=" << j;
    }
  }
}

TEST(BitwiseTruthTable, BinaryXorAllCells) {
  const Logic4Word expected[4][4] = {
      {kOut0, kOut1, kOutX, kOutX},
      {kOut1, kOut0, kOutX, kOutX},
      {kOutX, kOutX, kOutX, kOutX},
      {kOutX, kOutX, kOutX, kOutX},
  };
  for (int i = 0; i < 4; ++i) {
    for (int j = 0; j < 4; ++j) {
      auto r = Logic4Xor(kFour[i], kFour[j]);
      EXPECT_EQ(r.aval & 1u, expected[i][j].aval)
          << "row=" << i << " col=" << j;
      EXPECT_EQ(r.bval & 1u, expected[i][j].bval)
          << "row=" << i << " col=" << j;
    }
  }
}

TEST(BitwiseTruthTable, BinaryXnorAllCells) {
  const Logic4Word expected[4][4] = {
      {kOut1, kOut0, kOutX, kOutX},
      {kOut0, kOut1, kOutX, kOutX},
      {kOutX, kOutX, kOutX, kOutX},
      {kOutX, kOutX, kOutX, kOutX},
  };
  for (int i = 0; i < 4; ++i) {
    for (int j = 0; j < 4; ++j) {
      auto r = Logic4Not(Logic4Xor(kFour[i], kFour[j]));
      EXPECT_EQ(r.aval & 1u, expected[i][j].aval)
          << "row=" << i << " col=" << j;
      EXPECT_EQ(r.bval & 1u, expected[i][j].bval)
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
