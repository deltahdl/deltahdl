#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(EqualityWithUnknownBits, LogicalEqualityReturnsXWithUnknownOperand) {
  SimFixture f;

  MakeVar4(f, "el", 4, 0b1000, 0b0100);
  auto* b = f.ctx.CreateVariable("er", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "el"),
                          MakeId(f.arena, "er"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EqualityWithUnknownBits, LogicalInequalityReturnsXWithUnknownOperand) {
  SimFixture f;

  MakeVar4(f, "nl", 4, 0b1000, 0b0100);
  auto* b = f.ctx.CreateVariable("nr", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* expr = MakeBinary(f.arena, TokenKind::kBangEq, MakeId(f.arena, "nl"),
                          MakeId(f.arena, "nr"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EqualityWithUnknownBits, CaseEqualityAlwaysReturnsKnownValue) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqEq, MakeInt(f.arena, 5),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EqualityWithUnknownBits, CaseEqualityMatchesXZPatterns) {
  SimFixture f;

  MakeVar4(f, "a", 4, 0b1010, 0b0100);
  MakeVar4(f, "b", 4, 0b1010, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqEq, MakeId(f.arena, "a"),
                          MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EqualityWithUnknownBits, CaseEqualityMismatchesXZPatterns) {
  SimFixture f;

  MakeVar4(f, "a", 4, 0b1010, 0b0100);
  MakeVar4(f, "b", 4, 0b1010, 0b1000);
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqEq, MakeId(f.arena, "a"),
                          MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EqualityWithUnknownBits, CaseInequalityMatchesXZPatterns) {
  SimFixture f;

  MakeVar4(f, "a", 4, 0b1010, 0b0100);
  MakeVar4(f, "b", 4, 0b1010, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqEq, MakeId(f.arena, "a"),
                          MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EqualityWithUnknownBits, CaseInequalityMismatchesXZPatterns) {
  SimFixture f;

  MakeVar4(f, "a", 4, 0b1010, 0b0100);
  MakeVar4(f, "b", 4, 0b1010, 0b1000);
  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqEq, MakeId(f.arena, "a"),
                          MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(ExpressionSim, EqualityFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 == 8'd3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(ExpressionSim, InequalityFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 != 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(ExpressionSim, EqualityTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 == 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ExpressionSim, InequalityTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 != 8'd3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, BinaryCaseEq) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd7 === 8'd7);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, BinaryCaseNeq) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd7 !== 8'd3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, BinaryCaseEqFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd7 === 8'd3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(OperatorSim, BinaryCaseNeqFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd7 !== 8'd7);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EqualityOperatorEval, PackedStructEqualitySameValue) {
  SimFixture f;

  StructTypeInfo sinfo;
  sinfo.type_name = "my_struct";
  sinfo.total_width = 16;
  sinfo.is_packed = true;
  sinfo.fields.push_back({"a", 8, 8, DataTypeKind::kLogic});
  sinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("my_struct", sinfo);
  MakeVar(f, "s1", 16, 0xABCD);
  MakeVar(f, "s2", 16, 0xABCD);
  f.ctx.SetVariableStructType("s1", "my_struct");
  f.ctx.SetVariableStructType("s2", "my_struct");
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "s1"),
                          MakeId(f.arena, "s2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EqualityOperatorEval, PackedStructEqualityDiffValue) {
  SimFixture f;

  StructTypeInfo sinfo;
  sinfo.type_name = "my_struct";
  sinfo.total_width = 16;
  sinfo.is_packed = true;
  sinfo.fields.push_back({"a", 8, 8, DataTypeKind::kLogic});
  sinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("my_struct", sinfo);
  MakeVar(f, "s3", 16, 0xABCD);
  MakeVar(f, "s4", 16, 0x1234);
  f.ctx.SetVariableStructType("s3", "my_struct");
  f.ctx.SetVariableStructType("s4", "my_struct");
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "s3"),
                          MakeId(f.arena, "s4"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EqualityOperatorEval, PackedStructInequality) {
  SimFixture f;
  StructTypeInfo sinfo;
  sinfo.type_name = "my_struct";
  sinfo.total_width = 16;
  sinfo.is_packed = true;
  sinfo.fields.push_back({"a", 8, 8, DataTypeKind::kLogic});
  sinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("my_struct", sinfo);
  MakeVar(f, "s5", 16, 0xABCD);
  MakeVar(f, "s6", 16, 0x1234);
  f.ctx.SetVariableStructType("s5", "my_struct");
  f.ctx.SetVariableStructType("s6", "my_struct");
  auto* expr = MakeBinary(f.arena, TokenKind::kBangEq, MakeId(f.arena, "s5"),
                          MakeId(f.arena, "s6"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EqualityOperatorEval, SignedEqualityNegativeValues) {
  SimFixture f;
  MakeSignedVarAdv(f, "sa", 8, 0xFF);
  MakeSignedVarAdv(f, "sb", 8, 0xFF);
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RealOperandResult, RealEqualityComparison) {
  auto v = RunAndGet(
      "module t;\n"
      "  real a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 2.5;\n"
      "    b = 2.5;\n"
      "    r = (a == b);\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 1u);
}

TEST(RealOperandResult, RealInequalityComparison) {
  auto v = RunAndGet(
      "module t;\n"
      "  real a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 2.5;\n"
      "    b = 3.0;\n"
      "    r = (a != b);\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 1u);
}

TEST(RealOperandResult, MixedRealIntEqualityComparison) {
  auto v = RunAndGet(
      "module t;\n"
      "  real a;\n"
      "  int b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 3.0;\n"
      "    b = 3;\n"
      "    r = (a == b);\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 1u);
}

TEST(RealOperandResult, MixedRealIntInequalityComparison) {
  auto v = RunAndGet(
      "module t;\n"
      "  real a;\n"
      "  int b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 3.5;\n"
      "    b = 3;\n"
      "    r = (a != b);\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 1u);
}

TEST(EqualityOperatorEval, LogicalEqualityFalse) {
  SimFixture f;

  MakeVar(f, "a", 8, 5);
  MakeVar(f, "b", 8, 3);
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "a"),
                          MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EqualityOperatorEval, LogicalInequalityFalse) {
  SimFixture f;

  MakeVar(f, "a", 8, 5);
  MakeVar(f, "b", 8, 5);
  auto* expr = MakeBinary(f.arena, TokenKind::kBangEq, MakeId(f.arena, "a"),
                          MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EqualityOperatorEval, CaseEqualityFalseOnDifferentValues) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqEq, MakeInt(f.arena, 5),
                          MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EqualityOperatorEval, CaseInequalityFalseOnSameValues) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqEq, MakeInt(f.arena, 5),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EqualityOperatorEval, AllEqualityOperatorsReturnOneBit) {
  SimFixture f;

  MakeVar(f, "a", 32, 42);
  MakeVar(f, "b", 32, 42);

  auto* eq = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "a"),
                        MakeId(f.arena, "b"));
  EXPECT_EQ(EvalExpr(eq, f.ctx, f.arena).width, 1u);

  auto* neq = MakeBinary(f.arena, TokenKind::kBangEq, MakeId(f.arena, "a"),
                         MakeId(f.arena, "b"));
  EXPECT_EQ(EvalExpr(neq, f.ctx, f.arena).width, 1u);

  auto* ceq = MakeBinary(f.arena, TokenKind::kEqEqEq, MakeId(f.arena, "a"),
                         MakeId(f.arena, "b"));
  EXPECT_EQ(EvalExpr(ceq, f.ctx, f.arena).width, 1u);

  auto* cneq = MakeBinary(f.arena, TokenKind::kBangEqEq, MakeId(f.arena, "a"),
                          MakeId(f.arena, "b"));
  EXPECT_EQ(EvalExpr(cneq, f.ctx, f.arena).width, 1u);
}

}  // namespace
