// §6.20.2 Value parameters — the runtime value a parameter carries.
//
// A parameter's value is fixed during elaboration, but whether it survives to
// run time as the type it was declared with is a property of the lowering, so
// these tests read the value back out of a running module rather than
// inspecting the elaborated parameter. A real parameter is the case that
// distinguishes the two: an integer-only representation resolves it to
// something, or fails to resolve it at all, and either way the fraction is gone
// before any process can read it.
#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §6.20.2: "A parameter declared with a real type" takes a real value, so a
// fractional default must read back whole. A value truncated to an integer
// would display 2, and one that failed to resolve would leave the name
// undeclared and display 0.
TEST(ValueParameterSim, RealParameterKeepsItsFraction) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter real R = 2.5;\n"
                       "  initial $display(\"%g\", R);\n"
                       "endmodule\n",
                       f),
            "2.5\n");
}

// The localparam form of the same rule. §6.20.4 makes a localparam a parameter
// that cannot be overridden, not a different kind of value, so its real-ness is
// carried the same way -- and it is the form a nested expression is most likely
// to name.
TEST(ValueParameterSim, RealLocalparamKeepsItsFraction) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  localparam real R = 0.125;\n"
                       "  initial $display(\"%g\", R);\n"
                       "endmodule\n",
                       f),
            "0.125\n");
}

// §6.20.2 covers a value parameter wherever it is written, and a parameter port
// is the other place it can be written. The two positions are elaborated by
// different code, so a real value carried in one of them says nothing about the
// other, and this is the port half.
TEST(ValueParameterSim, RealParameterPortKeepsItsFraction) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t #(parameter real R = 1.5);\n"
                       "  initial $display(\"%g\", R);\n"
                       "endmodule\n",
                       f),
            "1.5\n");
}

// A real parameter whose default happens to have no fraction is still a real,
// so it divides as one. Reading the default as the integer it can also be
// spelled as would make this 0 -- which is why the real fold is tried before
// the integer fold rather than after it.
TEST(ValueParameterSim, RealParameterWithoutAFractionIsStillReal) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter real R = 2;\n"
                       "  initial $display(\"%g\", R / 4);\n"
                       "endmodule\n",
                       f),
            "0.5\n");
}

// The guard that carrying a real value did not disturb the integer path: an
// integer-typed parameter set from a real constant is still converted per
// §6.12.1 (round to nearest, ties away from zero), so 2.5 becomes 3.
TEST(ValueParameterSim, IntegerParameterFromRealConstantStillRounds) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter int N = 2.5;\n"
                       "  initial $display(\"%0d\", N);\n"
                       "endmodule\n",
                       f),
            "3\n");
}

// §6.20.2 (printed page 126): a parameter with a range specification has the
// range of its declaration, so a 96-bit localparam holds all 96 bits of its
// value. The three words are read back through part-selects, each a different
// value, so a value cut to 64 bits (hi reads 0) and one whose literal was lost
// whole (every word reads 0) are both told from the right one.
TEST(ValueParameterSim, WideLocalparamKeepsEveryWordOfItsValue) {
  SimFixture f;
  auto* hi = RunAndFindVar(
      "module t;\n"
      "  localparam logic [95:0] P = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  int hi, mid, lo;\n"
      "  initial begin\n"
      "    hi = P[95:64];\n"
      "    mid = P[63:32];\n"
      "    lo = P[31:0];\n"
      "  end\n"
      "endmodule\n",
      f, "hi");
  ASSERT_NE(hi, nullptr);
  EXPECT_EQ(hi->value.ToUint64(), 0x01234567u);
  auto* mid = f.ctx.FindVariable("mid");
  auto* lo = f.ctx.FindVariable("lo");
  ASSERT_NE(mid, nullptr);
  ASSERT_NE(lo, nullptr);
  EXPECT_EQ(mid->value.ToUint64(), 0x89ABCDEFu);
  EXPECT_EQ(lo->value.ToUint64(), 0x00112233u);
  EXPECT_FALSE(f.has_errors);
}

// §6.20.2 with §11.4.10: the same parameter as an operand, shifted by a whole
// word, so the high word is what the expression reads, not a part-select.
TEST(ValueParameterSim, WideParameterOperandCarriesItsHighWord) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  parameter logic [95:0] P = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  int y;\n"
      "  initial y = P >> 64;\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x01234567u);
  EXPECT_FALSE(f.has_errors);
}

// §6.20.2 (printed 126): a localparam set from another parameter takes that
// parameter's whole value, shifted here so the word read is not the one a
// copy of the low word alone would hold.
TEST(ValueParameterSim, WideLocalparamSetFromAWideParameterKeepsEveryWord) {
  SimFixture f;
  auto* hi = RunAndFindVar(
      "module t;\n"
      "  localparam logic [95:0] P = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  localparam logic [95:0] Q = P >> 8;\n"
      "  int hi;\n"
      "  initial hi = Q[95:64];\n"
      "endmodule\n",
      f, "hi");
  ASSERT_NE(hi, nullptr);
  EXPECT_EQ(hi->value.ToUint64(), 0x00012345u);
  EXPECT_FALSE(f.has_errors);
}

// §23.10.2 with §6.20.2 (printed 126): an instance's parameter value
// assignment does not change the declared range, so a 96-bit literal given to
// the instance reaches the instance whole. The override is folded on a path of
// its own, so the declaration test above says nothing about it.
TEST(ValueParameterSim, WideParameterOverriddenAtTheInstanceKeepsEveryWord) {
  SimFixture f;
  auto* hi = RunAndFindVar(
      "module c #(parameter logic [95:0] P = 96'h0);\n"
      "  int hi, lo;\n"
      "  initial begin\n"
      "    hi = P[95:64];\n"
      "    lo = P[31:0];\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  c #(.P(96'h0123_4567_89AB_CDEF_0011_2233)) u();\n"
      "endmodule\n",
      f, "u.hi");
  ASSERT_NE(hi, nullptr);
  EXPECT_EQ(hi->value.ToUint64(), 0x01234567u);
  auto* lo = f.ctx.FindVariable("u.lo");
  ASSERT_NE(lo, nullptr);
  EXPECT_EQ(lo->value.ToUint64(), 0x00112233u);
  EXPECT_FALSE(f.has_errors);
}

// §23.10.2: the override's expression is written in the instantiating module,
// so a parent's own 96-bit parameter handed down by name is read there, where
// it has storage, and not in the instance, which declares no K.
TEST(ValueParameterSim, WideParameterOverrideNamingTheParentsParameter) {
  SimFixture f;
  auto* hi = RunAndFindVar(
      "module c #(parameter logic [95:0] P = 96'h0);\n"
      "  int hi;\n"
      "  initial hi = P[95:64];\n"
      "endmodule\n"
      "module t;\n"
      "  localparam logic [95:0] K = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  c #(.P(K)) u();\n"
      "endmodule\n",
      f, "u.hi");
  ASSERT_NE(hi, nullptr);
  EXPECT_EQ(hi->value.ToUint64(), 0x01234567u);
  EXPECT_FALSE(f.has_errors);
}

// §6.20.2 (printed pages 126-127): a parameter declared with neither a type
// nor a range takes the type and range of its final value, so `parameter p1 =
// 13'h7e` is a 13-bit logic vector, `newconst3 = 3'h4` a 3-bit one and
// `newconst4 = 4`, whose value is unsized, at least 32 bits; a parameter
// declared with a range, `[31:0] dec_const = 1'b1`, has its declaration's 32
// whatever the value's size, and `signed [3:0]` its four. These are the
// clause's own examples, read with $bits inside the module, and every
// untyped parameter answered 32 while the lowering gave one 32 bits whenever
// the declaration fixed no width. %h of p1 prints the four digits its 13 bits
// need, not the eight of a 32-bit word, and the second line reads the values
// through the same storage: $signed(4'b1100 + mux_selector) is -4 at the
// operands' four bits, byte_mask is 7 from `byte_size - 1`.
TEST(ValueParameterSim, UntypedParameterIsAsWideAsItsSizedLiteral) {
  SimFixture f;
  std::string printed = RunCapture(
      "module t;\n"
      "  parameter p1 = 13'h7e;\n"
      "  parameter [31:0] dec_const = 1'b1;\n"
      "  parameter newconst3 = 3'h4;\n"
      "  parameter newconst4 = 4;\n"
      "  parameter signed [3:0] mux_selector = 0;\n"
      "  parameter real r1 = 3.5e17;\n"
      "  parameter msb = 7;\n"
      "  parameter e = 25, f = 9;\n"
      "  parameter byte_size = 8, byte_mask = byte_size - 1;\n"
      "  initial begin\n"
      "    $display(\"p1=%0d dec=%0d new3=%0d new4=%0d msel=%0d rbits=%0d\",\n"
      "             $bits(p1), $bits(dec_const), $bits(newconst3),\n"
      "             $bits(newconst4), $bits(mux_selector), $bits(r1));\n"
      "    $display(\"sel=%0d s=%0d e=%0d f=%0d bm=%0d p1=%h new3=%b\",\n"
      "             $signed(4'b1100 + mux_selector), msb, e, f, byte_mask,\n"
      "             p1, newconst3);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed,
            "p1=13 dec=32 new3=3 new4=32 msel=4 rbits=64\n"
            "sel=-4 s=7 e=25 f=9 bm=7 p1=007e new3=100\n");
  EXPECT_FALSE(f.has_errors);
}

// §6.20.2 (printed pages 126-127): the final value is the one after every
// override, so a parameter port declared `parameter P = 13'h7e` is 13 bits
// wide in an instance that keeps the default and 5 bits wide in one that
// overrides it with 5'd9 (§23.10.2, printed 766); a value's type includes its
// sign, so `parameter N = -1` is a signed 32-bit vector that prints -1, and a
// bare `signed` with no range, `parameter signed S = 4'sd7`, has the range of
// its value, four bits, where the lowering read the implicit type's one bit.
TEST(ValueParameterSim, UntypedParameterPortTakesTheWidthOfItsFinalValue) {
  SimFixture f;
  std::string printed = RunCapture(
      "module c #(parameter P = 13'h7e);\n"
      "  initial $display(\"P=%0d\", $bits(P));\n"
      "endmodule\n"
      "module t;\n"
      "  parameter N = -1;\n"
      "  parameter signed S = 4'sd7;\n"
      "  c u1();\n"
      "  c #(.P(5'd9)) u2();\n"
      "  initial begin\n"
      "    #1 $display(\"N=%0d nb=%0d S=%0d sb=%0d\", N, $bits(N), S, "
      "$bits(S));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed, "P=13\nP=5\nN=-1 nb=32 S=7 sb=4\n");
  EXPECT_FALSE(f.has_errors);
}

// §6.20.2 (printed pages 126-127): a parameter declared with neither type nor
// range takes the type of its final value, and a real value makes it a real
// parameter, so `parameter r = 5.7` -- the clause's own example, which its
// comment calls a real parameter -- reads 5.7, and `average_delay = (r + f)
// / 2`, real arithmetic on it with the integer f of 9, is the real 7.35,
// which $rtoi truncates to 7. Both read 0 while a real fold was tried for a
// declared real type alone and an untyped parameter's real literal folded
// as no integer at all, and while a fold reading a real parameter's name
// found the 0 its integer slot holds: `twice = r1 * 2` from the declared
// `real r1 = 3.5e17` is 7.0e17, and the conversion of §6.12.1, which the
// clause applies to parameters, rounds `int ri = r` to 6.
TEST(ValueParameterSim, UntypedParameterWithARealValueIsReal) {
  SimFixture f;
  std::string printed = RunCapture(
      "module t;\n"
      "  parameter r = 5.7;\n"
      "  parameter e = 25, f = 9;\n"
      "  parameter average_delay = (r + f) / 2;\n"
      "  parameter real r1 = 3.5e17;\n"
      "  parameter twice = r1 * 2;\n"
      "  parameter int ri = r;\n"
      "  initial $display(\"r=%f avg=%0d avgr=%f twice=%0d ri=%0d e=%0d\", r,\n"
      "                   $rtoi(average_delay), average_delay,\n"
      "                   twice == 7.0e17, ri, e);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed, "r=5.700000 avg=7 avgr=7.350000 twice=1 ri=6 e=25\n");
  EXPECT_FALSE(f.has_errors);
}

// §6.20.1 (printed page 125) writes the same declarations in a parameter port
// list, so an untyped port whose default is real arithmetic on an earlier
// real port, `parameter b = a * 2` after `parameter real a = 1.5`, is the
// real 3.0 in the instance, and an untyped port with a real literal default,
// `parameter c = 0.25`, reads 0.25 in an instance that keeps the default.
TEST(ValueParameterSim, UntypedParameterPortWithARealDefaultIsReal) {
  SimFixture f;
  std::string printed = RunCapture(
      "module c #(parameter real a = 1.5, parameter b = a * 2,\n"
      "           parameter c = 0.25);\n"
      "  initial $display(\"b=%f c=%f\", b, c);\n"
      "endmodule\n"
      "module t;\n"
      "  c u();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed, "b=3.000000 c=0.250000\n");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
