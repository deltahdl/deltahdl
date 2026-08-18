// Further tests for §9.4.2.3 "Conditional event controls", continuing
// test_simulator_subclause_09_04_02_03a.cpp.
//
// The cases here are the ones the guard can get wrong without any of the
// straightforward ones noticing: a condition whose truth is decided above the
// low 64 bits, a condition that is high-impedance rather than unknown, an
// operand that is a named event rather than a value-carrying variable, the
// precedence of `iff` over `or` written the way the clause writes it, and a
// procedural `@` statement rather than an `always` block.

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §9.4.2.3 refers the truth of the guard to §12.4, which makes any nonzero
// value true. The guard here is nonzero only above the low 64 bits, so an
// implementation that judges truth from a 64-bit projection of the value calls
// it false and never runs the body.
TEST(ConditionalEventIffSim, IffConditionSetAboveLow64BitsFires) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [64:0] enable;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    clk = 0; enable = 0; count = 0;\n"
      "    enable[64] = 1'b1;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff enable)\n"
      "    count = count + 1;\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §12.4: a nonzero value is true whichever of its bits are set, so a guard of
// 8'hFE is true even though its low bit is zero. An implementation that read
// the guard's low bit alone would suppress the body here.
TEST(ConditionalEventIffSim, IffMultiBitGuardWithLowBitClearFires) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] enable;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    clk = 0; enable = 8'hFE; count = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff enable)\n"
      "    count = count + 1;\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §12.4 makes z false as it makes x false, and the two are separate values.
// A guard held at high impedance therefore suppresses the body.
TEST(ConditionalEventIffSim, IffConditionHighImpedanceSuppresses) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic enable;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    clk = 0; enable = 1'bz; count = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff enable)\n"
      "    count = count + 1;\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §9.4.2.3: "the event expression only triggers if the expression after the
// iff is true". A named event is an event expression like any other, so a
// trigger arriving while the guard is false leaves the waiting process where
// it was. Both triggers here arrive with `en` at zero.
TEST(ConditionalEventIffSim, IffOnNamedEventFalseSuppresses) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event e;\n"
      "  logic en;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    en = 0; count = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    @(e iff en);\n"
      "    count = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> e;\n"
      "    #1 -> e;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §9.4.2.3: the same wait resumes on a trigger that arrives while the guard is
// true, so the guard gates the named event rather than disabling it.
TEST(ConditionalEventIffSim, IffOnNamedEventTrueResumes) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event e;\n"
      "  logic en;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    en = 1; count = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    @(e iff en);\n"
      "    count = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> e;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §9.4.2.3: "iff has precedence over or", so `@(a iff c or b)` is
// `@((a iff c) or b)` and the guard covers `a` alone. `c` stays zero
// throughout: the change to `a` is suppressed and the change to `b` is not, so
// the body runs exactly once. A guard read as covering the whole list would
// suppress both and leave the count at zero.
TEST(ConditionalEventIffSim, IffGuardsOnlyItsOwnOperandOfAnOrList) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic a, b, c;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    a = 0; b = 0; c = 0; count = 0;\n"
      "    #1 a = 1;\n"
      "    #1 b = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(a iff c or b)\n"
      "    count = count + 1;\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §9.4.2.3: the qualifier belongs to the event control and not to the `always`
// block, so a procedural `@` statement is gated the same way. Neither edge here
// arrives with the guard true, and the statement after the wait never runs.
TEST(ConditionalEventIffSim, ProceduralEventControlIffFalseKeepsWaiting) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk, en;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    clk = 0; en = 0; count = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge clk iff en);\n"
      "    count = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 clk = 1;\n"
      "    #1 clk = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §9.4.2.3: the same procedural wait resumes on the edge that arrives with the
// guard true, which is what says the suppression above is the guard doing its
// work rather than the wait never resuming at all.
TEST(ConditionalEventIffSim, ProceduralEventControlIffTrueResumes) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk, en;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    clk = 0; en = 1; count = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge clk iff en);\n"
      "    count = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
