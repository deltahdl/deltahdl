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

// §11.7: the value `$signed` returns is signed and the value `$unsigned`
// returns is unsigned, so an assignment that stores such a value has to keep
// that signedness whatever the width of the variable it is stored in. The
// three tests below read `var->value.is_signed`, the flag on the vector the
// run stored, and never a flag off an evaluated expression. EvalIdentifier in
// src/simulator/evaluation.cpp writes `val.is_signed = var->is_signed` on
// every read of a variable, so an expression naming the variable reports the
// signedness of the declaration and says nothing about what was stored.

// The eight-bit variable is resized by ResizeNarrowKnown in
// src/simulator/statement_assign.cpp, the path ResizeToWidth takes for a value
// with no x or z that fits in 64 bits.
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

// The ninety-six-bit variable is resized by the other path of ResizeToWidth,
// the one that builds its result with MakeLogic4Vec. Neither this test nor the
// narrow one above states the rule alone. Together they say the two paths
// answer alike, so the one assignment does not store the signed value
// $signed returns as signed in a wide variable and as unsigned in a narrow one.
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

// §11.7: `$unsigned` returns an unsigned value, so the stored flag is false.
// This is the test that fails if the two paths of ResizeToWidth are made to
// agree by setting the flag on every value they store.
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

}  // namespace
