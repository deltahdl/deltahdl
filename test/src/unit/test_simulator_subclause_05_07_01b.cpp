#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "helpers_scheduler.h"

namespace {

TEST(IntegerLiteralSim, SimpleDecimalNumber) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 659;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 659u);
}

TEST(IntegerLiteralSim, SizedBinaryLiteral) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 4'b1001;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 9u);
}

TEST(IntegerLiteralSim, SizedOctalLiteral) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial x = 12'o7460;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 07460u);
}

TEST(IntegerLiteralSim, SizedDecimalLiteral) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 5'd3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 3u);
}

TEST(IntegerLiteralSim, UnsizedHexLiteral) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 'h837FF;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x837FFu);
}

TEST(IntegerLiteralSim, UnsizedOctalLiteral) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 'o7460;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 07460u);
}

TEST(IntegerLiteralSim, TruncationFromLeft) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 4'b11001;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x09u);
}

TEST(IntegerLiteralSim, SignedBasedLiteral) {
  auto result = RunAndGet(
      "module t;\n"
      "  integer x;\n"
      "  initial x = 4'shf;\n"
      "endmodule\n",
      "x");
  uint32_t mask = 0xFFFFFFFF;
  EXPECT_EQ(result & mask, mask);
}

TEST(IntegerLiteralSim, SizeConstantNonzero) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 1'b1;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 1u);
}

TEST(IntegerLiteralSim, LiteralInTernaryCondition) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 1 ? 8'd99 : 8'd0;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(v, 99u);
}

TEST(IntegerLiteralSim, LeftPadZWhenLeftmostIsZ) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hz5;\n"
      "endmodule\n",
      "x");

  EXPECT_EQ(result & 0x0Fu, 0x05u);
}

TEST(IntegerLiteralSim, UnsizedDefaultWidth32Bits) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 'hFFFF_FFFF;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0xFFFFFFFFu);
}

TEST(IntegerLiteralSim, SizedHexLiteralValue) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 20'h837FF;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x837FFu);
}

TEST(IntegerLiteralSim, UnsizedValueAboveU32WidensBeyond32Bits) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [63:0] x;\n"
      "  initial x = 'h1_0000_0000;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x100000000ull);
}

TEST(IntegerLiteralSim, SimpleDecimalNegativeSignExtends) {
  auto result = RunAndGet(
      "module t;\n"
      "  integer x;\n"
      "  initial x = -1;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFFFFFFFu, 0xFFFFFFFFu);
}

TEST(IntegerLiteralSim, BaseOnlyDoesNotSignExtend) {
  auto result = RunAndGet(
      "module t;\n"
      "  integer x;\n"
      "  initial x = 4'hf;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFFFFFFFu, 0x0000000Fu);
}

TEST(IntegerLiteralSim, NegativeSizedLiteralIsTwosComplement) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = -8'sd6;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFu, 0xFAu);
}

TEST(IntegerLiteralSim, SignedLiteralSignExtendsIntoUnsignedLogic) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 4'shf;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFu, 0xFFu);
}

TEST(IntegerLiteralSim, UnsignedLiteralZeroExtendsIntoUnsignedLogic) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 4'hf;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFu, 0x0Fu);
}

TEST(IntegerLiteralSim, UnbasedUnsizedIsOneBitInConcatenation) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = {1'b1, '1, 1'b0};\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x6u);
}

TEST(IntegerLiteralSim, UnbasedUnsizedIsOneBitInReplication) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = {4{'1}};\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0xFu);
}

TEST(IntegerLiteralSim, NegativeLiteralSignExtendsIntoWiderLogic) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = -4'sd1;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFu, 0xFFu);
}

TEST(IntegerLiteralSim, UnsizedSignedValueReservesSignBit) {
  auto result = RunAndGet(
      "module t;\n"
      "  longint x;\n"
      "  initial x = 2147483648;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 2147483648ull);
}

TEST(IntegerLiteralSim, UnsizedHexLiteralIsAsWideAsItsDigitsNeed) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [63:0] n;\n"
      "  initial n = {$bits('hF_FFFF_FFFF_FFFF_FFFF), $bits('h7_0000_0000)};\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(result, 0x0000004400000023u);
}

TEST(IntegerLiteralSim, SignedLiteralInitializerSignExtendsIntoInt) {
  auto result = RunAndGet(
      "module t;\n"
      "  int c = 4'shf;\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(result & 0xFFFFFFFFu, 0xFFFFFFFFu);
}

TEST(IntegerLiteralSim, SignedLiteralInitializerSignExtendsIntoInteger) {
  auto result = RunAndGet(
      "module t;\n"
      "  integer g = 4'shf;\n"
      "endmodule\n",
      "g");
  EXPECT_EQ(result & 0xFFFFFFFFu, 0xFFFFFFFFu);
}

TEST(IntegerLiteralSim, SignedLiteralInitializerSignExtendsIntoWiderLogic) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] b = 4'shf;\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(result & 0xFFFFu, 0xFFFFu);
}

TEST(IntegerLiteralSim, SignedHexLiteralInitializerSignExtendsHighByte) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] d = 8'sh85;\n"
      "endmodule\n",
      "d");
  EXPECT_EQ(result & 0xFFFFu, 0xFF85u);
}

TEST(IntegerLiteralSim, NegativeSignedLiteralInitializerSignExtendsIntoInt) {
  auto result = RunAndGet(
      "module t;\n"
      "  int f = -8'sd6;\n"
      "endmodule\n",
      "f");
  EXPECT_EQ(result & 0xFFFFFFFFu, 0xFFFFFFFAu);
}

TEST(IntegerLiteralSim, UnsignedLiteralInitializerZeroExtendsIntoWiderLogic) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] e = 8'h85;\n"
      "endmodule\n",
      "e");
  EXPECT_EQ(result & 0xFFFFu, 0x0085u);
}

TEST(IntegerLiteralSim,
     NegativeUnsignedLiteralInitializerNegatesAtTargetWidth) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] a = -8'd6;\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result & 0xFFFFu, 0xFFFAu);
}

TEST(IntegerLiteralSim,
     NegativeUnsignedLiteralParameterNegatesAtDeclaredWidth) {
  auto result = RunAndGet(
      "module t;\n"
      "  parameter logic [15:0] V = -8'd6;\n"
      "  logic [15:0] a = V;\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result & 0xFFFFu, 0xFFFAu);
}

TEST(IntegerLiteralSim, NegativeUnsignedLiteralClassPropertyNegatesAtWidth) {
  auto result = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    logic [15:0] v = -8'd6;\n"
      "  endclass\n"
      "  logic [15:0] a;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    a = c.v;\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result & 0xFFFFu, 0xFFFAu);
}

TEST(IntegerLiteralSim, NegativeUnsignedLiteralAboveHalfRangeNegatesAtWidth) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] a = -8'd130;\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result & 0xFFFFu, 0xFF7Eu);
}

TEST(IntegerLiteralSim, BitwiseNotOfSizedLiteralInvertsAtTargetWidth) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] a = ~8'hFF;\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result & 0xFFFFu, 0xFF00u);
}

TEST(IntegerLiteralSim, UnbasedUnsizedOneFillsARangedParameter) {
  auto result = RunAndGet(
      "module t;\n"
      "  parameter logic [7:0] Q = '1;\n"
      "  logic [15:0] a = Q;\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result & 0xFFFFu, 0xFFu);
}

TEST(IntegerLiteralSim, UnbasedUnsizedOneFillsAFourBitParameter) {
  auto result = RunAndGet(
      "module t;\n"
      "  parameter logic [3:0] U = '1;\n"
      "  logic [15:0] a = U;\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result & 0xFFFFu, 0xFu);
}

TEST(IntegerLiteralSim, UnbasedUnsizedOneIsOneBitInAnUntypedParameter) {
  auto result = RunAndGet(
      "module t;\n"
      "  parameter R = '1;\n"
      "  logic [63:0] a = R;\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result, 1u);
}

TEST(IntegerLiteralSim, UnbasedUnsizedOneFillsALocalparam) {
  auto result = RunAndGet(
      "module t;\n"
      "  localparam logic [7:0] P = '1;\n"
      "  logic [15:0] a = P;\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result & 0xFFFFu, 0xFFu);
}

TEST(IntegerLiteralSim, UnbasedUnsizedXFillsAnIntegerParameterWithX) {
  auto result = RunAndGet(
      "module t;\n"
      "  parameter integer S = 'x;\n"
      "  logic a;\n"
      "  initial a = (S === 32'bx);\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result, 1u);
}

TEST(IntegerLiteralSim, SizedXLiteralFillsAParameterWithX) {
  auto result = RunAndGet(
      "module t;\n"
      "  parameter logic [7:0] S = 8'hx;\n"
      "  logic a;\n"
      "  initial a = (S === 8'bx);\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result, 1u);
}

TEST(IntegerLiteralSim, UnbasedUnsizedOneFillsAParameterPortDefault) {
  auto result = RunAndGet(
      "module m #(parameter logic [7:0] A = '1);\n"
      "  logic [15:0] a = A;\n"
      "endmodule\n"
      "module t;\n"
      "  m u ();\n"
      "endmodule\n",
      "u.a");
  EXPECT_EQ(result & 0xFFFFu, 0xFFu);
}

TEST(IntegerLiteralSim, UnbasedUnsizedOneFillsAPackageParameter) {
  auto result = RunAndGet(
      "package p;\n"
      "  parameter logic [11:0] W = '1;\n"
      "endpackage\n"
      "module t;\n"
      "  logic [63:0] a = p::W;\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result, 0xFFFu);
}

TEST(IntegerLiteralSim, UnbasedUnsizedOneFillsAParameterPastSixtyFourBits) {
  const std::string kSrc =
      "module t;\n"
      "  parameter logic [95:0] G = '1;\n"
      "  logic [31:0] hi = G[95:64];\n"
      "  logic [63:0] lo = G[63:0];\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "hi"), 0xFFFFFFFFu);
  EXPECT_EQ(RunAndGet(kSrc, "lo"), ~uint64_t{0});
}

TEST(IntegerLiteralSim, UnbasedUnsizedOneIsOneBitUnderBits) {
  auto result = RunAndGet(
      "module t;\n"
      "  int b;\n"
      "  initial b = $bits('1);\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(result, 1u);
}

TEST(IntegerLiteralSim, UnbasedUnsizedXIsOneBitUnderBits) {
  auto result = RunAndGet(
      "module t;\n"
      "  int b;\n"
      "  initial b = $bits('x);\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(result, 1u);
}

TEST(IntegerLiteralSim, UnbasedUnsizedOneEqualsAOneBitOne) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic c;\n"
      "  initial c = ('1 == 1'b1);\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(result, 1u);
}

TEST(IntegerLiteralSim, UnbasedUnsizedOneFormatsAsOne) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic c;\n"
      "  initial c = ($sformatf(\"%0d\", '1) == \"1\");\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(result, 1u);
}

TEST(IntegerLiteralSim, UnbasedUnsizedOneFillsTheOperandItIsComparedWith) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x = 8'hff;\n"
      "  logic c;\n"
      "  initial c = (x == '1);\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(result, 1u);
}

TEST(IntegerLiteralSim, UnbasedUnsizedOneCaseItemFillsTheSelectorWidth) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x = 8'hff;\n"
      "  logic [7:0] y;\n"
      "  initial case (x)\n"
      "    '1: y = 8'd1;\n"
      "    default: y = 8'd0;\n"
      "  endcase\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(result & 0xFFu, 1u);
}

TEST(IntegerLiteralSim, UnbasedUnsizedOneFillsAFormalArgument) {
  auto result = RunAndGet(
      "module t;\n"
      "  function logic [7:0] f(input logic [7:0] a);\n"
      "    return a;\n"
      "  endfunction\n"
      "  logic [7:0] y;\n"
      "  initial y = f('1);\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(result & 0xFFu, 0xFFu);
}

TEST(IntegerLiteralSim, UnbasedUnsizedOneNonblockingFillsPastSixtyFourBits) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [127:0] w;\n"
      "  logic [63:0] hi;\n"
      "  initial begin\n"
      "    w <= '1;\n"
      "    #1 hi = w[127:64];\n"
      "  end\n"
      "endmodule\n",
      "hi");
  EXPECT_EQ(result, ~uint64_t{0});
}

TEST(IntegerLiteralSim, OneBitVariableSetFromUnbasedUnsizedOneReadsAsOne) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic a = '1;\n"
      "  logic [7:0] b;\n"
      "  initial b = a;\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(result & 0xFFu, 1u);
}

TEST(IntegerLiteralSim, OneBitPropertySetFromUnbasedUnsizedOneReadsAsOne) {
  auto result = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    logic en;\n"
      "  endclass\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    c.en = '1;\n"
      "    b = c.en;\n"
      "  end\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(result & 0xFFu, 1u);
}

TEST(IntegerLiteralSim, UnbasedUnsizedOneFillsAPropertyAssignedThroughAHandle) {
  auto result = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    logic [7:0] v;\n"
      "  endclass\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    c.v = '1;\n"
      "    b = c.v;\n"
      "  end\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(result & 0xFFu, 0xFFu);
}

TEST(IntegerLiteralSim, UnbasedUnsizedOneFillsAClassParameterDefault) {
  auto result = RunAndGet(
      "module t;\n"
      "  class C #(parameter logic [7:0] INIT = '1);\n"
      "    logic [7:0] v = INIT;\n"
      "  endclass\n"
      "  logic [15:0] a;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    a = c.v;\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result & 0xFFFFu, 0xFFu);
}

TEST(IntegerLiteralSim, UnbasedUnsizedOneFillsAClassParameterSizedByAnother) {
  auto result = RunAndGet(
      "module t;\n"
      "  class C #(parameter int W = 8, parameter logic [W-1:0] INIT = '1);\n"
      "    logic [15:0] v = INIT;\n"
      "  endclass\n"
      "  logic [15:0] a;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    a = c.v;\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result & 0xFFFFu, 0xFFu);
}

TEST(IntegerLiteralSim, UnbasedUnsizedOneFillsAClassParameterReadByScope) {
  auto result = RunAndGet(
      "module t;\n"
      "  class C #(parameter int W = 8, parameter logic [W-1:0] INIT = '1);\n"
      "    static function logic [15:0] get(); return INIT; endfunction\n"
      "  endclass\n"
      "  logic [15:0] a;\n"
      "  initial a = C#()::get();\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result & 0xFFFFu, 0xFFu);
}

TEST(IntegerLiteralSim, ClassParameterOverrideIsCutToTheDeclaredWidth) {
  auto result = RunAndGet(
      "module t;\n"
      "  class C #(parameter int W = 8, parameter logic [W-1:0] INIT = '1);\n"
      "    function logic [31:0] get(); return INIT; endfunction\n"
      "  endclass\n"
      "  logic [31:0] a;\n"
      "  initial begin\n"
      "    C #(12, 'hfff0) c;\n"
      "    c = new;\n"
      "    a = c.get();\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result & 0xFFFFFFFFu, 0xFF0u);
}

TEST(IntegerLiteralSim, UnbasedUnsizedOneFillsAPackageParameterSizedByAnother) {
  auto result = RunAndGet(
      "package p;\n"
      "  parameter int N = 12;\n"
      "  parameter logic [N-1:0] M = '1;\n"
      "endpackage\n"
      "module t;\n"
      "  logic [15:0] a = p::M;\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result & 0xFFFFu, 0xFFFu);
}

TEST(IntegerLiteralSim, UnsizedBinaryXHighDigitExtendsWithXInAnInitializer) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] a = 'bx1;\n"
      "  logic c;\n"
      "  initial c = ($sformatf(\"%b\", a) == \"xxxxxxx1\");\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(result, 1u);
}

TEST(IntegerLiteralSim, UnsizedBinaryZHighDigitExtendsWithZInAnInitializer) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] b = 'bz10;\n"
      "  logic c;\n"
      "  initial c = ($sformatf(\"%b\", b) == \"zzzzzz10\");\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(result, 1u);
}

TEST(IntegerLiteralSim,
     UnsizedOctalXDigitBelowAZeroSetsThreeBitsInAnInitializer) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] o = 'o0x1;\n"
      "  logic c;\n"
      "  initial c = ($sformatf(\"%b\", o) == \"00xxx001\");\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(result, 1u);
}

TEST(IntegerLiteralSim, UnsizedHexXFillsAnEightBitInitializer) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] d = 'hx;\n"
      "  logic c;\n"
      "  initial c = ($sformatf(\"%b\", d) == \"xxxxxxxx\");\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(result, 1u);
}

TEST(IntegerLiteralSim, UnsizedHexZExtendsASixtyFourBitInitializer) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [63:0] w = 'hz;\n"
      "  logic c;\n"
      "  initial c = ($sformatf(\"%h\", w) == \"zzzzzzzzzzzzzzzz\");\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(result, 1u);
}

TEST(IntegerLiteralSim, BlockCommentBetweenSizeAndBaseReadsTheSizedValue) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8 /* c */ 'h11;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 17u);
}

TEST(IntegerLiteralSim, BlockCommentBetweenSizeAndBaseKeepsTheSizeSigned) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial x = 4 /* c */ 'shf;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0xFFFFu);
}

TEST(IntegerLiteralSim, LineCommentBetweenSizeAndBaseReadsTheSizedValue) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8 // c\n"
      "    'h11;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 17u);
}

}  // namespace
