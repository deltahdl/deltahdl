#include <gtest/gtest.h>

#include <string>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(SignedExprSim, SystemTfCallUnsigned) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = $unsigned(8'sd5);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(SignedExprSim, UnsignedPreservesValue) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$unsigned", {MakeInt(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(SignedExprSim, SignedPreservesValue) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$signed", {MakeInt(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(SignedExprSim, SignedSetsSignedFlag) {
  SimFixture f;
  MakeVar(f, "a", 8, 0xAB);
  auto* expr = MakeSysCall(f.arena, "$signed", {MakeId(f.arena, "a")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
  EXPECT_EQ(result.ToUint64(), 0xABu);
  EXPECT_EQ(result.width, 8u);
}

TEST(SignedExprSim, UnsignedClearsSignedFlag) {
  SimFixture f;
  MakeSignedVarAdv(f, "a", 8, 0xAB);
  auto* expr = MakeSysCall(f.arena, "$unsigned", {MakeId(f.arena, "a")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
  EXPECT_EQ(result.ToUint64(), 0xABu);
  EXPECT_EQ(result.width, 8u);
}

TEST(SignedExprSim, SignedPreservesWidth) {
  SimFixture f;
  MakeVar(f, "w", 16, 0x1234);
  auto* expr = MakeSysCall(f.arena, "$signed", {MakeId(f.arena, "w")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0x1234u);
}

TEST(SignedExprSim, UnsignedPreservesWidth) {
  SimFixture f;
  MakeSignedVarAdv(f, "w", 16, 0x1234);
  auto* expr = MakeSysCall(f.arena, "$unsigned", {MakeId(f.arena, "w")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0x1234u);
}

TEST(SignedExprSim, SignedOnAlreadySignedIsNoop) {
  SimFixture f;
  MakeSignedVarAdv(f, "s", 8, 0xFF);
  auto* expr = MakeSysCall(f.arena, "$signed", {MakeId(f.arena, "s")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
  EXPECT_EQ(result.width, 8u);
}

TEST(SignedExprSim, UnsignedOnAlreadyUnsignedIsNoop) {
  SimFixture f;
  MakeVar(f, "u", 8, 0xFF);
  auto* expr = MakeSysCall(f.arena, "$unsigned", {MakeId(f.arena, "u")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
  EXPECT_EQ(result.width, 8u);
}

TEST(SignedExprSim, SignedPreservesBitPattern) {
  SimFixture f;
  MakeVar(f, "v", 8, 0b11001010);
  auto* expr = MakeSysCall(f.arena, "$signed", {MakeId(f.arena, "v")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 0b11001010u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(SignedExprSim, UnsignedPreservesBitPattern) {
  SimFixture f;
  MakeSignedVarAdv(f, "v", 8, 0b11001010);
  auto* expr = MakeSysCall(f.arena, "$unsigned", {MakeId(f.arena, "v")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 0b11001010u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(SignedExprSim, EmptyArgsReturnsZero) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$signed", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SignedExprSim, UnsignedOfNegativeFour) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] regA;\n"
      "  initial regA = $unsigned(-4);\n"
      "endmodule\n",
      f, "regA");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFCu);
}

TEST(SignedExprSim, SignedOfFourBitVector) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [7:0] regS;\n"
      "  initial regS = $signed(4'b1100);\n"
      "endmodule\n",
      f, "regS");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFCu);
}

TEST(SignedExprSim, SignedAdditionEndToEnd) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] regA, regB;\n"
      "  logic signed [7:0] regS;\n"
      "  initial begin\n"
      "    regA = 8'hFF;\n"
      "    regB = 8'h01;\n"
      "    regS = $signed(regA) + $signed(regB);\n"
      "  end\n"
      "endmodule\n",
      f, "regS");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(SignedExprSim, SystemTfCallSigned) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [7:0] x;\n"
      "  initial x = $signed(8'd200);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 200u);
}

TEST(SignedExprSim, UnsignedOfNegativeSizedSignedLiteral) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] regB;\n"
      "  initial regB = $unsigned(-4'sd4);\n"
      "endmodule\n",
      f, "regB");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0Cu);
}

TEST(SignedExprSim, UnsignedOfNegativeSizedSignedLiteralAsParameter) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  localparam [7:0] P = $unsigned(-4'sd4);\n"
      "  logic [7:0] regB;\n"
      "  initial regB = P;\n"
      "endmodule\n",
      f, "regB");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0Cu);
}

TEST(SignedExprSim, SignedOfFourBitVectorAsParameter) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  localparam signed [7:0] P = $signed(4'b1100);\n"
      "  logic signed [7:0] regS;\n"
      "  initial regS = P;\n"
      "endmodule\n",
      f, "regS");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFCu);
}

TEST(SignedExprSim, UnsignedOfNegativeFourAsParameter) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  localparam [7:0] P = $unsigned(-4);\n"
      "  logic [7:0] regA;\n"
      "  initial regA = P;\n"
      "endmodule\n",
      f, "regA");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFCu);
}

TEST(SignedExprSim, SignedOfConcatenationKeepsConcatenationWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [1:0] hi, lo;\n"
      "  logic signed [7:0] regS;\n"
      "  initial begin\n"
      "    hi = 2'b11;\n"
      "    lo = 2'b00;\n"
      "    regS = $signed({hi, lo});\n"
      "  end\n"
      "endmodule\n",
      f, "regS");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFCu);
}

TEST(SignedExprSim, SignedOfPartSelectKeepsSelectedWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  logic signed [7:0] regS;\n"
      "  initial begin\n"
      "    v = 8'b10101100;\n"
      "    regS = $signed(v[3:0]);\n"
      "  end\n"
      "endmodule\n",
      f, "regS");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFCu);
}

TEST(SignedExprSim, StoredValueOfNarrowSignedVariableIsSigned) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [7:0] narrow;\n"
      "  initial narrow = $signed(4'b1100);\n"
      "endmodule\n",
      f, "narrow");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.is_signed);
}

TEST(SignedExprSim, StoredValueOfWideSignedVariableIsSigned) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [95:0] wide;\n"
      "  initial wide = $signed(4'b1100);\n"
      "endmodule\n",
      f, "wide");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.is_signed);
}

TEST(SignedExprSim, StoredValueOfUnsignedVariableIsUnsigned) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] plain;\n"
      "  initial plain = $unsigned(4'b1100);\n"
      "endmodule\n",
      f, "plain");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.is_signed);
}

TEST(SignedExprSim, TheSignCastsGiveTheExamplesValuesWhereverTheyAreWritten) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "package pk;\n"
          "  localparam logic signed [7:0] PS = $signed(4'b1100);\n"
          "endpackage\n"
          "class K;\n"
          "  static function int f(logic [3:0] v);\n"
          "    logic signed [7:0] t;\n"
          "    t = $signed(v);\n"
          "    return t;\n"
          "  endfunction\n"
          "endclass\n"
          "module m;\n"
          "  logic [7:0] regA, regB;\n"
          "  logic signed [7:0] regS;\n"
          "  logic signed [15:0] w;\n"
          "  logic [3:0] xz = 4'b1x0z;\n"
          "  typedef struct packed { logic [1:0] h; logic [1:0] l; } s_t;\n"
          "  s_t st = 4'b1010;\n"
          "  logic [1:0][1:0] pa = 4'b1001;\n"
          "  localparam logic signed [7:0] LS = $signed(4'b1100);\n"
          "  localparam logic [7:0] LU = $unsigned(-4'sd4);\n"
          "  function automatic int g(logic [3:0] v); return $signed(v); "
          "endfunction\n"
          "  initial begin\n"
          "    regA = $unsigned(-4); regB = $unsigned(-4'sd4);\n"
          "    regS = $signed(4'b1100);\n"
          "    $display(\"%b %b %0d\", regA, regB, regS);\n"
          "    regA = unsigned'(-4); regS = signed'(4'b1100);\n"
          "    $display(\"%b %0d\", regA, regS);\n"
          "    regA = 8'hF0; regB = 8'h20;\n"
          "    w = regA + regB; $write(\"%0d \", w);\n"
          "    w = byte'(regA) + byte'(regB); $write(\"%0d \", w);\n"
          "    w = signed'(regA) + signed'(regB); $write(\"%0d \", w);\n"
          "    w = $signed(regA) + $signed(regB); $display(\"%0d\", w);\n"
          "    $display(\"%b %b %0d %0d\", $signed(xz), "
          "$unsigned($signed(xz)),\n"
          "             $bits($signed(st)), $bits($unsigned(pa)));\n"
          "    w = $signed(st); $write(\"%0d \", w);\n"
          "    w = $signed(pa); $write(\"%0d \", w);\n"
          "    w = $unsigned(4'sb1000); $display(\"%0d\", w);\n"
          "    $display(\"%0d %0d %0d %0d %0d\", LS, LU, pk::PS, "
          "K::f(4'b1100),\n"
          "             g(4'b1100));\n"
          "  end\n"
          "endmodule\n",
          f),
      "11111100 00001100 -4\n11111100 -4\n272 16 16 16\n1x0z 1x0z 4 4\n"
      "-6 -7 8\n-4 12 -4 -4 -4\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
