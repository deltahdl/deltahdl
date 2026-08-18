#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"

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

// §11.7: `regB = $unsigned(-4'sd4);` gives `8'b00001100`. This is the line of
// the clause's example that separates a correct conversion from one that
// widens its operand: `-4'sd4` is four bits wide, so the eight-bit target is
// filled by zero-extending the unsigned value the conversion produced. An
// implementation that let the operand's signedness survive would sign-extend
// instead and leave `8'b11111100`.
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

// §11.7 in a constant expression: a parameter's value is folded at elaboration
// rather than evaluated at run time, and the conversion has to mean the same
// thing in both. The four bits 1100 read unsigned are 12, so the parameter is
// `8'b00001100` as the procedural assignment above is.
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

// §11.7: the same for `$signed`, whose result is the operand's bits read as a
// signed number. The four bits 1100 read signed are -4, which fills an
// eight-bit target as `8'b11111100`.
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

// §11.7: `$unsigned(-4)` in a constant expression. `-4` is thirty-two bits
// wide, so the eight-bit parameter keeps its low byte, `8'b11111100`. Read
// beside the four-bit case above, this pair says the answer follows the
// operand's width rather than the sign of the number written.
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

// §11.7: the operand is any expression, and its width is whatever that
// expression is worth. A concatenation is four bits here, so `$signed` reads
// those four bits as -4 and the target is filled by sign-extending them.
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

// §11.7: a part-select is as wide as the range it names, so `$signed` on the
// low four bits of an eight-bit value reads four bits and not eight. Reading
// eight would make the result 8'b10101100 rather than -4.
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

}  // namespace
