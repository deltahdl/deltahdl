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

}  // namespace
