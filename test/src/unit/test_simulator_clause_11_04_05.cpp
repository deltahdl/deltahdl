#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// §11.4.5: for the logical equality (==) and inequality (!=) operators, if an
// unknown (x) or high-impedance (z) bit makes the relation ambiguous, the
// result shall be 1'bx. The x bit is produced by a 4-state literal stored into
// a declared variable and read back as an operand, so the whole path from
// source through elaboration and simulation is exercised.
TEST(EqualityOperatorSim, LogicalEqualityAmbiguousXOperandYieldsX) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b1x00;\n"
      "    b = 4'b1000;\n"
      "    r = (a == b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  // An x result is flagged by its unknown (bval) bit being set.
  EXPECT_NE(r->value.words[0].bval & 1u, 0u);
}

TEST(EqualityOperatorSim, LogicalInequalityAmbiguousZOperandYieldsX) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b1000;\n"
      "    b = 4'b10z0;\n"
      "    r = (a != b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  EXPECT_NE(r->value.words[0].bval & 1u, 0u);
}

// §11.4.5: for case equality (===) and case inequality (!==), the x and z bits
// participate in the comparison and must match for the operands to be equal;
// the result is always a known 1'b1 or 1'b0, never x. Both operands here carry
// identical x and z bits, so === reports a known match.
TEST(EqualityOperatorSim, CaseEqualityMatchesXZFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b1x0z;\n"
      "    b = 4'b1x0z;\n"
      "    r = (a === b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
  // The result is a known value: no unknown bit is set.
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
}

TEST(EqualityOperatorSim, CaseEqualityXZMismatchIsKnownFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b1x0z;\n"
      "    b = 4'b1x00;\n"
      "    r = (a === b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 0u);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
}

TEST(EqualityOperatorSim, CaseInequalityXZMismatchIsKnownTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b1x0z;\n"
      "    b = 4'b1x00;\n"
      "    r = (a !== b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
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

// §11.4.5: when both operands are signed, the comparison is a signed one and
// the narrower operand is sign-extended to the wider width. Here a is 4-bit
// signed -1 (1111); extended to 8 bits it becomes 0xFF, which equals the 8-bit
// signed -1. A zero-extension would give 0x0F and mismatch, so a result of 1
// confirms the sign-extending path. Both operands are declared signed so the
// signedness is produced by real source, not asserted synthetically.
TEST(EqualityOperatorSim, BothSignedSignExtendsNarrowerOperand) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [3:0] a;\n"
      "  logic signed [7:0] b;\n"
      "  logic y;\n"
      "  initial begin\n"
      "    a = -1;\n"
      "    b = -1;\n"
      "    y = (a == b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

// §11.4.5: the signed comparison distinguishes a sign-extended negative from a
// same-low-bits positive. a is 4-bit signed -1 -> 0xFF; b is 8-bit signed 15 ->
// 0x0F. As signed values -1 != 15, so the result is 0. Were a zero-extended, it
// would read 0x0F and spuriously match, so 0 confirms the signed
// interpretation.
TEST(EqualityOperatorSim, BothSignedNegativeDiffersFromPositive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [3:0] a;\n"
      "  logic signed [7:0] b;\n"
      "  logic y;\n"
      "  initial begin\n"
      "    a = -1;\n"
      "    b = 15;\n"
      "    y = (a == b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0u);
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

TEST(EqualityOperatorSim, UnsignedZeroExtendsSmallerOperand) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  logic [7:0] wide;\n"
      "  logic y;\n"
      "  initial begin\n"
      "    narrow = 4'b1111;\n"
      "    wide   = 8'h0F;\n"
      "    y = (narrow == wide);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

TEST(EqualityOperatorSim, UnsignedNarrowMismatchesWiderTopBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  logic [7:0] wide;\n"
      "  logic y;\n"
      "  initial begin\n"
      "    narrow = 4'b1111;\n"
      "    wide   = 8'hFF;\n"
      "    y = (narrow == wide);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0u);
}

// §11.4.5: when one operand is unsigned, the whole comparison is unsigned and
// the narrower operand is zero-extended (never sign-extended). a is 4-bit
// signed -1 (0xF); mixed with the unsigned 8-bit b it is zero-extended to
// 0x0F (15), which equals b. A both-signed reading would sign-extend a to 0xFF
// and mismatch, so a result of 1 confirms the unsigned interpretation forced by
// the single unsigned operand.
TEST(EqualityOperatorSim, MixedSignedUnsignedComparesUnsigned) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic signed [3:0] a;\n"
      "  logic [7:0] b;\n"
      "  logic y;\n"
      "  initial begin\n"
      "    a = -1;\n"
      "    b = 8'h0F;\n"
      "    y = (a == b);\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(v, 1u);
}

// §11.4.5: signedness that comes from a default-signed integer type (rather
// than an explicit 'signed' keyword) still drives a signed comparison that
// sign-extends the narrower operand. byte -1 (0xFF) sign-extends to 32 bits
// (0xFFFFFFFF) and equals int -1. Were byte treated as unsigned it would read
// 0x000000FF and mismatch, so 1 confirms the signed interpretation taken from
// the type default.
TEST(EqualityOperatorSim, DefaultSignedTypesSignExtend) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte a;\n"
      "  int b;\n"
      "  logic y;\n"
      "  initial begin\n"
      "    a = -1;\n"
      "    b = -1;\n"
      "    y = (a == b);\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(v, 1u);
}

// §11.4.5: case inequality (!==) on two operands that carry identical x and z
// bits reports a known 1'b0 -- they match bit for bit, including the unknowns.
// Completes the !== input form alongside the === match and === /!== mismatch
// cases; the result is always known, never x.
TEST(EqualityOperatorSim, CaseInequalityMatchesXZIsKnownFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b1x0z;\n"
      "    b = 4'b1x0z;\n"
      "    r = (a !== b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 0u);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
}

}  // namespace
