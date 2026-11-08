#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "lexer/token.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

void ExpectKnownTrue(SimFixture& f, std::string_view name) {
  auto* r = f.ctx.FindVariable(name);
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
}

TEST(EqualityOperatorSim, LogicalEqualityAmbiguousXOperandYieldsX) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b1x00;\n"
      "    b = 4'b1000;\n"
      "    r = (a == b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  EXPECT_NE(r->value.words[0].bval & 1u, 0u);
}

TEST(EqualityOperatorSim, LogicalInequalityAmbiguousZOperandYieldsX) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b1000;\n"
      "    b = 4'b10z0;\n"
      "    r = (a != b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  EXPECT_NE(r->value.words[0].bval & 1u, 0u);
}

void ExpectKnownEquality(std::string_view a, std::string_view b,
                         std::string_view op, uint64_t want) {
  SimFixture f;
  auto* r = RunAndFindVar(std::string("module t;\n"
                                      "  logic [7:0] a, b;\n"
                                      "  logic r;\n"
                                      "  initial begin\n"
                                      "    a = ") +
                              std::string(a) + ";\n    b = " + std::string(b) +
                              ";\n    r = (a " + std::string(op) +
                              " b);\n"
                              "  end\n"
                              "endmodule\n",
                          f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(r->value.ToUint64(), want);
}

TEST(EqualityOperatorSim, LogicalEqualityKnownMismatchBesideAnXIsFalse) {
  ExpectKnownEquality("8'b1101x001", "8'b1101x000", "==", 0);
}

TEST(EqualityOperatorSim, LogicalEqualityKnownMismatchBesideAZIsFalse) {
  ExpectKnownEquality("8'b1101z001", "8'b1101z000", "==", 0);
}

TEST(EqualityOperatorSim, LogicalInequalityKnownMismatchBesideAnXIsTrue) {
  ExpectKnownEquality("8'b1101x001", "8'b1101x000", "!=", 1);
}

TEST(EqualityOperatorSim, CaseEqualityMatchesXZFromSource) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b1x0z;\n"
      "    b = 4'b1x0z;\n"
      "    r = (a === b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
}

TEST(EqualityOperatorSim, CaseEqualityXZMismatchIsKnownFalse) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b1x0z;\n"
      "    b = 4'b1x00;\n"
      "    r = (a === b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 0u);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
}

TEST(EqualityOperatorSim, CaseInequalityXZMismatchIsKnownTrue) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b1x0z;\n"
      "    b = 4'b1x00;\n"
      "    r = (a !== b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
}

TEST(EqualityOperatorSim,
     CaseEqualityMatchesDefaultInitialValueOfArrayElement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] s;\n"
      "  logic [7:0] arr [0:2];\n"
      "  logic r1, r2;\n"
      "  initial begin\n"
      "    r1 = (arr[0] === 8'hxx);\n"
      "    r2 = (arr[0] === s);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ASSERT_NO_FATAL_FAILURE(ExpectKnownTrue(f, "r1"));
  ASSERT_NO_FATAL_FAILURE(ExpectKnownTrue(f, "r2"));
}

TEST(EqualityOperatorSim, CaseEqualityMatchesAllXProducedByUnaryMinus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  logic r1;\n"
      "  initial begin\n"
      "    a = 4'b1x0z;\n"
      "    r1 = ((-a) === 4'bxxxx);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ASSERT_NO_FATAL_FAILURE(ExpectKnownTrue(f, "r1"));
}

TEST(ExpressionSim, EqualityFalse) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 == 8'd3);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(ExpressionSim, InequalityFalse) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 != 8'd5);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(ExpressionSim, EqualityTrue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 == 8'd5);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ExpressionSim, InequalityTrue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 != 8'd3);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, BinaryCaseEq) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd7 === 8'd7);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, BinaryCaseNeq) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd7 !== 8'd3);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, BinaryCaseEqFalse) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd7 === 8'd3);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(OperatorSim, BinaryCaseNeqFalse) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd7 !== 8'd7);\n"
      "endmodule\n",
      f, "x");
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

TEST(EqualityOperatorSim, BothSignedSignExtendsNarrowerOperand) {
  SimFixture f;
  auto* y = RunAndFindVar(
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
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

TEST(EqualityOperatorSim, BothSignedNegativeDiffersFromPositive) {
  SimFixture f;
  auto* y = RunAndFindVar(
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
      f, "y");
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
  auto* y = RunAndFindVar(
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
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

TEST(EqualityOperatorSim, UnsignedNarrowMismatchesWiderTopBits) {
  SimFixture f;
  auto* y = RunAndFindVar(
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
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0u);
}

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

TEST(EqualityOperatorSim, CaseInequalityMatchesXZIsKnownFalse) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b1x0z;\n"
      "    b = 4'b1x0z;\n"
      "    r = (a !== b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 0u);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
}

TEST(EqualityOperatorSim, AnUnpackedArrayEqualsAPatternElementByElement) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef int arr_t[3];\n"
      "  arr_t v = '{1, 2, 3}, w = '{2, 2, 2}, u = '{2, 2, 3};\n"
      "  function automatic bit alltwo(arr_t a);\n"
      "    return a == arr_t'{3{2}};\n"
      "  endfunction\n"
      "  class C; int a[3] = '{1, 2, 3}; endclass\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    $display(\"%0d %0d %0d %0d\", v == arr_t'{1, 2, 3},\n"
      "             v == arr_t'{9, 9, 3}, v != arr_t'{1, 2, 4},\n"
      "             v != arr_t'{1, 2, 3});\n"
      "    $display(\"%0d %0d %0d\", alltwo(w), alltwo(u),\n"
      "             h.a == arr_t'{1, 2, 3});\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 0 1 0\n1 0 1\n");
}

}  // namespace
