#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// --- Logical/relational on real → single-bit result ---

TEST(RealOperandResult, RelationalLtOnRealIsSingleBit) {
  SimFixture f;
  MakeRealVar(f, "a", 1.5);
  MakeRealVar(f, "b", 2.5);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kLt,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RealOperandResult, RelationalGtOnRealIsSingleBit) {
  SimFixture f;
  MakeRealVar(f, "a", 3.0);
  MakeRealVar(f, "b", 2.0);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kGt,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RealOperandResult, RelationalLtEqOnRealIsSingleBit) {
  SimFixture f;
  MakeRealVar(f, "a", 2.0);
  MakeRealVar(f, "b", 2.0);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kLtEq,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RealOperandResult, RelationalGtEqOnRealIsSingleBit) {
  SimFixture f;
  MakeRealVar(f, "a", 1.0);
  MakeRealVar(f, "b", 2.0);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kGtEq,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(RealOperandResult, RelationalMixedRealIntIsSingleBit) {
  SimFixture f;
  MakeRealVar(f, "r", 2.5);
  MakeVar(f, "i", 32, 3);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kLt,
                                    MakeId(f.arena, "r"), MakeId(f.arena, "i")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RealOperandResult, LogicalAndOnRealIsSingleBit) {
  SimFixture f;
  MakeRealVar(f, "a", 1.5);
  MakeRealVar(f, "b", 2.5);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kAmpAmp,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RealOperandResult, LogicalOrOnRealIsSingleBit) {
  SimFixture f;
  MakeRealVar(f, "a", 0.0);
  MakeRealVar(f, "b", 2.5);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPipePipe,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RealOperandResult, LogicalNotOnRealIsSingleBit) {
  SimFixture f;
  MakeRealVar(f, "a", 0.0);
  auto result = EvalExpr(MakeUnary(f.arena, TokenKind::kBang,
                                   MakeId(f.arena, "a")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RealOperandResult, LogicalNotOnNonzeroRealIsFalse) {
  SimFixture f;
  MakeRealVar(f, "a", 3.14);
  auto result = EvalExpr(MakeUnary(f.arena, TokenKind::kBang,
                                   MakeId(f.arena, "a")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// --- Equality on real operands → single-bit, compared as double values ---

TEST(RealOperandResult, EqualityOnRealIsSingleBit) {
  SimFixture f;
  MakeRealVar(f, "a", 2.5);
  MakeRealVar(f, "b", 2.5);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kEqEq,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RealOperandResult, InequalityOnRealIsSingleBit) {
  SimFixture f;
  MakeRealVar(f, "a", 2.5);
  MakeRealVar(f, "b", 3.0);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kBangEq,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// --- End-to-end simulation tests ---

TEST(RealOperandResult, E2eRealAddResult) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 1.5 + 2.25;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 3.75);
}

TEST(RealOperandResult, E2eRealSubResult) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 5.0 - 1.75;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 3.25);
}

TEST(RealOperandResult, E2eRealMulResult) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 2.5 * 4.0;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 10.0);
}

TEST(RealOperandResult, E2eRealDivResult) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 7.0 / 2.0;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 3.5);
}

TEST(RealOperandResult, E2eRelationalOnRealIsSingleBit) {
  auto v = RunAndGet(
      "module t;\n"
      "  real a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 3.14;\n"
      "    b = 2.71;\n"
      "    r = a > b;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 1u);
}

TEST(RealOperandResult, E2eLogicalAndOnRealIsSingleBit) {
  auto v = RunAndGet(
      "module t;\n"
      "  real a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 1.0;\n"
      "    b = 0.0;\n"
      "    r = a && b;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0u);
}

TEST(RealOperandResult, E2eUnaryMinusOnReal) {
  auto v = RunAndGetReal(
      "module t;\n"
      "  real a, b;\n"
      "  initial begin\n"
      "    a = 3.5;\n"
      "    b = -a;\n"
      "  end\n"
      "endmodule\n",
      "b");
  EXPECT_DOUBLE_EQ(v, -3.5);
}

}  // namespace
