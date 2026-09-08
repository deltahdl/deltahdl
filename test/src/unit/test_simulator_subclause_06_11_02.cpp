#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(TwoStateAndFourState, UnsignedWideningZeroExtends) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [3:0] src;\n"
      "  bit [7:0] dst;\n"
      "  initial begin\n"
      "    src = 4'hA;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0x0Au);
}

TEST(TwoStateAndFourState, SignedWideningSignExtends) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte src;\n"
      "  int dst;\n"
      "  initial begin\n"
      "    src = -2;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFEu);
}

TEST(TwoStateAndFourState, NarrowingTruncatesMSBs) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [7:0] src;\n"
      "  bit [3:0] dst;\n"
      "  initial begin\n"
      "    src = 8'hAB;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 4u);
  EXPECT_EQ(var->value.ToUint64(), 0xBu);
}

TEST(TwoStateAndFourState, FourToTwoStateZeroesOnlyXzBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  bit [7:0] dst;\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

TEST(TwoStateAndFourState, FourStateVariableHoldsXAndZ) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  initial a = 4'b1x0z;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "1x0z");
}

TEST(TwoStateAndFourState, IntegerKeepsXzThatIntZeroes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  int two_state;\n"
      "  integer four_state;\n"
      "  initial begin\n"
      "    src = 8'bxxxxxxxx;\n"
      "    two_state = src;\n"
      "    four_state = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* two = f.ctx.FindVariable("two_state");
  auto* four = f.ctx.FindVariable("four_state");
  ASSERT_NE(two, nullptr);
  ASSERT_NE(four, nullptr);
  EXPECT_TRUE(two->value.IsKnown());
  EXPECT_EQ(two->value.ToUint64(), 0u);
  EXPECT_FALSE(four->value.IsKnown());
}

TEST(TwoStateAndFourState, PositiveSignedWideningFillsZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte src;\n"
      "  int dst;\n"
      "  initial begin\n"
      "    src = 8'sd5;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0x00000005u);
}

TEST(TwoStateAndFourState, LogicAndRegSimulateIdentically) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  reg [7:0] b;\n"
      "  initial begin\n"
      "    a = 8'hCA;\n"
      "    b = 8'hCA;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), vb->value.ToUint64());
  EXPECT_EQ(va->value.width, vb->value.width);
}

TEST(TwoStateAndFourState, MultiWordSignedWideningSignExtends) {
  SimFixture f;
  auto* dst = RunAndFindVar(
      "module t;\n"
      "  bit signed [31:0]  src;\n"
      "  bit signed [127:0] dst;\n"
      "  initial begin\n"
      "    src = 32'sh80000000;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(dst, nullptr);
  EXPECT_EQ(dst->value.width, 128u);
  ASSERT_EQ(dst->value.nwords, 2u);

  EXPECT_EQ(dst->value.words[0].aval, 0xFFFFFFFF80000000ull);
  EXPECT_EQ(dst->value.words[1].aval, 0xFFFFFFFFFFFFFFFFull);
}

TEST(TwoStateAndFourState, MultiWordNarrowingTruncatesMSBs) {
  SimFixture f;
  auto* dst = RunAndFindVar(
      "module t;\n"
      "  bit [127:0] src;\n"
      "  bit [31:0]  dst;\n"
      "  initial begin\n"
      "    src = 128'hAAAAAAAA_BBBBBBBB_CCCCCCCC_DDDDDDDD;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(dst, nullptr);
  EXPECT_EQ(dst->value.width, 32u);
  EXPECT_EQ(dst->value.ToUint64(), 0xDDDDDDDDu);
}

TEST(TwoStateAndFourState, MultiWordFourToTwoStateZeroesXz) {
  SimFixture f;
  auto* dst = RunAndFindVar(
      "module t;\n"
      "  logic [127:0] src;\n"
      "  bit   [127:0] dst;\n"
      "  initial begin\n"
      "    src = {64'hxxxxxxxxxxxxxxxx, 64'hCAFEBABEDEADBEEF};\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(dst, nullptr);
  EXPECT_EQ(dst->value.width, 128u);
  ASSERT_EQ(dst->value.nwords, 2u);
  EXPECT_TRUE(dst->value.IsKnown());
  EXPECT_EQ(dst->value.words[0].aval, 0xCAFEBABEDEADBEEFull);
  EXPECT_EQ(dst->value.words[1].aval, 0ull);
}

// The x/z-to-zero conversion also applies when a 4-state value initializes a
// 2-state variable at declaration, not only in a procedural assignment. Widths
// match here so the numeric-projection path does not mask the coercion.
TEST(TwoStateAndFourState, TwoStateInitializerZeroesXz) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] a = 8'b1010_x10z;\n"
      "  bit       b = 1'bx;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_TRUE(va->value.IsKnown());
  EXPECT_EQ(va->value.ToUint64(), 0xA4u);
  EXPECT_TRUE(vb->value.IsKnown());
  EXPECT_EQ(vb->value.ToUint64(), 0u);
}

// A 4-state variable keeps the same x/z initializer, discriminating the guard
// against the 2-state coercion above.
TEST(TwoStateAndFourState, FourStateInitializerKeepsXz) {
  SimFixture f;
  auto* va = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a = 8'b1010_x10z;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(va, nullptr);
  EXPECT_FALSE(va->value.IsKnown());
  EXPECT_EQ(va->value.ToString(), "1010x10z");
}

// reg is one of the four 4-state types, so it retains x and z like logic.
TEST(TwoStateAndFourState, RegHoldsXAndZ) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  reg [3:0] a;\n"
      "  initial a = 4'b1x0z;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "1x0z");
}

// time is the fourth 4-state type; unknown bits survive rather than coercing.
TEST(TwoStateAndFourState, TimeHoldsXAndZ) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  time ts;\n"
      "  initial ts = 64'b1x0z;\n"
      "endmodule\n",
      f, "ts");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 64u);
  EXPECT_FALSE(var->value.IsKnown());
}

// A 2-state byte destination forces the incoming unknown/high-Z bits to zero.
TEST(TwoStateAndFourState, ByteConversionZeroesXz) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  byte dst;\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

// Same conversion into a 16-bit 2-state shortint destination.
TEST(TwoStateAndFourState, ShortintConversionZeroesXz) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] src;\n"
      "  shortint dst;\n"
      "  initial begin\n"
      "    src = 16'b0000_0000_1010_x10z;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0x00A4u);
}

// Same conversion into a 64-bit 2-state longint destination.
TEST(TwoStateAndFourState, LongintConversionZeroesXz) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [63:0] src;\n"
      "  longint dst;\n"
      "  initial begin\n"
      "    src = 64'b1010_x10z;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

// The widening direction depends on signedness (§6.11.3): an explicit unsigned
// override on a normally-signed byte zero-extends instead of sign-extending.
// The same 0xFF bits sign-extend to 0xFFFFFFFF when the byte stays signed.
TEST(TwoStateAndFourState, UnsignedByteWideningZeroExtends) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte unsigned src;\n"
      "  int dst;\n"
      "  initial begin\n"
      "    src = 8'hFF;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0x000000FFu);
}

// §6.11.2's conversion applies to an assignment wherever it is written, and a
// subroutine body runs on the statement executor in eval_function_body.cpp
// rather than the one FourToTwoStateZeroesOnlyXzBits above exercises. That
// executor converted nowhere, and it also left every body local at Variable's
// 4-state default, so both halves are read below: the target's flag, which the
// lowerer sets for a variable of the design, and the flag a local gets when the
// subroutine declares it.

// The target is a `bit` of the design, written from a function body. Its flag
// was already right; what was missing was the conversion at the write.
TEST(TwoStateAndFourState, FunctionBodyZeroesXzIntoATwoStateTarget) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  bit [7:0] dst;\n"
      "  function void copy();\n"
      "    dst = src;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    copy();\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

// The other half: a `bit` local the subroutine declares. Its flag is what the
// declaration sets, and the value is carried out through a 4-state variable so
// that what is read is the local's own conversion and not a second one.
TEST(TwoStateAndFourState, FunctionBodyTwoStateLocalZeroesXz) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] dst;\n"
      "  function void copy();\n"
      "    bit [7:0] tmp;\n"
      "    tmp = src;\n"
      "    dst = tmp;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    copy();\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

// §6.11.2 names `logic` among the types that do have unknown values, so a
// 4-state local keeps what a 2-state one loses. Without this the two cases
// above would also pass a body that converted every local it declared.
TEST(TwoStateAndFourState, FunctionBodyFourStateLocalKeepsXz) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] dst;\n"
      "  function void copy();\n"
      "    logic [7:0] tmp;\n"
      "    tmp = src;\n"
      "    dst = tmp;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    copy();\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "1010x10z");
}

// The limit the declaration accepts. Is4stateType is asked of the type's kind
// alone, and a name answers false whatever it stands for, so a local declared
// with a typedef of `logic` is left 4-state rather than converted on that
// answer. This case is that choice: the unknowns survive, which is the smaller
// error than clearing the unknowns of a type that has them. #3486 is what would
// carry the name's resolved kind this far.
TEST(TwoStateAndFourState, FunctionBodyLocalOfATypedefNameKeepsXz) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef logic [7:0] octet;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] dst;\n"
      "  function void copy();\n"
      "    octet tmp;\n"
      "    tmp = src;\n"
      "    dst = tmp;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    copy();\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "1010x10z");
}

// A subroutine creates two more objects the clause governs and neither carried
// its state-ness: the formal a value is copied into, and the implicit variable
// §13.4.1 gives the function's return type. Both were left at Variable's
// 4-state default, so an unknown passed to a `bit` formal or returned from a
// `bit` function was kept where the same value assigned to a `bit` of the
// design was cleared.

// §10.8 makes "the passing of a value to a subroutine input, output, or inout
// argument" an assignment-like context, so the conversion belongs at the copy
// in. The formal is read back out through a 4-state variable, so what is read
// is the formal's own conversion and not a second one at the target.
TEST(TwoStateAndFourState, TwoStateFormalZeroesXzAtTheCall) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] dst;\n"
      "  function void take(input bit [7:0] p);\n"
      "    dst = p;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    take(src);\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

// The same call with a 4-state formal, which keeps what the 2-state one loses.
// Without this a copy that converted every formal would pass the case above.
TEST(TwoStateAndFourState, FourStateFormalKeepsXzAtTheCall) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] dst;\n"
      "  function void take(input logic [7:0] p);\n"
      "    dst = p;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    take(src);\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "1010x10z");
}

// §13.4.1's implicit variable, written by a return statement. ExecFuncReturn
// resizes to the declared return width and wrote the result straight into the
// variable, so this is the one write in a subroutine body that the identifier
// assignment's conversion does not stand for.
TEST(TwoStateAndFourState, TwoStateFunctionReturnZeroesXz) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] dst;\n"
      "  function bit [7:0] pass();\n"
      "    return src;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    dst = pass();\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

// The same variable written by name rather than by a return statement, which
// §13.4.1 gives as the other way to set it. That write reaches
// ExecFuncIdentifierAssign, so it converts on the flag rather than on a
// conversion of its own, and it is the flag that both forms needed.
TEST(TwoStateAndFourState, TwoStateFunctionNameAssignZeroesXz) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] dst;\n"
      "  function bit [7:0] pass();\n"
      "    pass = src;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    dst = pass();\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

// §6.11.2, printed p.110: "any unknown or high-impedance bits shall be
// converted to zeros." The rule is stated of the 2-state type of the object
// written, and an element of an unpacked array is an object of the array's
// element type, so how many dimensions the declaration wrote cannot change the
// answer. It did. The two-dimensional leaf carried the declaration's 2-state
// flag and coerced; the one-dimensional leaf was created without it and
// defaulted to 4-state, so the coercion never fired and the same 8'hxx stayed
// unknown in c[0] while it read zero in d[0][0]. Both spellings are written in
// the one run, and both asserted, so the case states the disagreement rather
// than one half of it.
//
// ToUint64 is no use here: it projects aval & ~bval, so an x reads as zero
// whether or not it was converted, and every one of these cases would have
// passed unconverted. ToString reads the bval plane, which is the plane the
// conversion clears.
TEST(TwoStateAndFourState, TwoStateUnpackedElementZeroesXzAtEitherRank) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] c [0:1];\n"
      "  bit [7:0] d [0:1][0:1];\n"
      "  initial begin\n"
      "    c[0] = 8'hxx;\n"
      "    d[0][0] = 8'hxx;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* vc = f.ctx.FindVariable("c[0]");
  auto* vd = f.ctx.FindVariable("d[0][0]");
  ASSERT_NE(vc, nullptr);
  ASSERT_NE(vd, nullptr);
  EXPECT_EQ(vc->value.ToString(), "00000000");
  EXPECT_EQ(vd->value.ToString(), vc->value.ToString());
}

// The clause names "unknown or high-impedance" bits together and converts both,
// and only the bval plane tells the two apart: x is (aval=1, bval=1) and z is
// (aval=0, bval=1). A value that is all z therefore sets a bit pattern the x
// case above never reaches -- every aval bit clear -- and pins that the rule's
// second word is covered too, rather than leaving z to the coercion's
// arithmetic by inference.
TEST(TwoStateAndFourState, TwoStateUnpackedElementZeroesHighImpedance) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [7:0] c [0:1];\n"
      "  initial c[1] = 8'hzz;\n"
      "endmodule\n",
      f, "c[1]");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0u);
}

// The guard on the two above: §6.11.2 converts what a 2-state type stores, and
// says nothing about a 4-state one, whose whole point is to hold these bits. An
// element of a logic array is a 4-state object, so it keeps a mixed x/z pattern
// unchanged. A fix that gave every array leaf the conversion rather than giving
// each leaf its declaration's own state count would read 10100100 here.
TEST(TwoStateAndFourState, FourStateUnpackedElementKeepsXz) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] e [0:1];\n"
      "  initial e[0] = 8'b1010_x10z;\n"
      "endmodule\n",
      f, "e[0]");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "1010x10z");
}

// §6.8 makes a variable declaration assignment an assignment to the declared
// variable, so §6.11.2's conversion is owed by a declaration exactly as it is
// owed by the statement below it. A subroutine-body local recorded the flag the
// conversion is made through and stored its initializer without applying it,
// which is what makes the two spellings of one declaration disagree: the second
// case here is the same two facts as two statements and answered 0 all along.
TEST(TwoStateAndFourState, TwoStateBodyLocalDropsItsInitializersUnknownBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] seed;\n"
      "  int result;\n"
      "  function void probe();\n"
      "    int v = seed;\n"
      "    result = $isunknown(v);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    seed = 8'b1x0z0000;\n"
      "    probe();\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// The spelling that already converted, which is what the case above has to
// agree with rather than merely answer correctly on its own.
TEST(TwoStateAndFourState, TwoStateBodyLocalAssignedAfterDeclarationDropsThem) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] seed;\n"
      "  int result;\n"
      "  function void probe();\n"
      "    int v;\n"
      "    v = seed;\n"
      "    result = $isunknown(v);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    seed = 8'b1x0z0000;\n"
      "    probe();\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// The bits the conversion keeps: §6.11.2 zeroes the unknown ones and leaves the
// known ones alone, so a case asserting only that nothing is unknown would pass
// on a local that came out all zeros.
TEST(TwoStateAndFourState, TwoStateBodyLocalKeepsTheKnownBitsOfItsInitializer) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] seed;\n"
      "  int result;\n"
      "  function void probe();\n"
      "    int v = seed;\n"
      "    result = v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    seed = 8'b1010_x10z;\n"
      "    probe();\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

// §10.5 makes a variable declaration assignment "a special case of procedural
// assignment", so §6.11.2's conversion reaches an array's initializer element
// by element -- §10.9.1 evaluating each pattern item in the assignment context
// of its element. The three helpers that fill a one-dimensional array's leaves
// stored the item resized and not converted, so the one spelling that is both a
// declaration initializer and an array element kept the x that the same value
// loses in a scalar declaration and in a runtime write to the same element.
TEST(TwoStateAndFourState, TwoStateArrayPositionalInitDropsUnknownBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [7:0] c [0:1] = '{8'hxx, 8'h00};\n"
      "endmodule\n",
      f, "c[0]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "00000000");
}

// §10.9.1's replication form, whose item is stored by a second helper.
TEST(TwoStateAndFourState, TwoStateArrayReplicatedInitDropsUnknownBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [7:0] c [0:1] = '{2{8'hxx}};\n"
      "endmodule\n",
      f, "c[0]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "00000000");
}

// §10.9.1's default key, whose item is stored by a third helper again.
TEST(TwoStateAndFourState, TwoStateArrayDefaultKeyedInitDropsUnknownBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [7:0] c [0:1] = '{default: 8'hxx};\n"
      "endmodule\n",
      f, "c[0]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "00000000");
}

// The guard: §6.11.2 converts on the way into a 2-state type and only there, so
// a 4-state element keeps every bit its initializer gave it. Without this the
// three above would pass on a helper that zeroed unconditionally.
TEST(TwoStateAndFourState, FourStateArrayPositionalInitKeepsUnknownBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] d [0:1] = '{8'hxx, 8'h00};\n"
      "endmodule\n",
      f, "d[0]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "xxxxxxxx");
}

// The initializer item is a bare name here, which EvalExpr answers with that
// variable's own Logic4Vec, and the conversion writes in place: through a
// shared buffer it would clear the source's own unknown bits, which §6.8 keeps
// as the source's to hold.
TEST(TwoStateAndFourState, TwoStateArrayInitLeavesItsSourceVariableAlone) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] s = 8'hxx;\n"
      "  bit [7:0] c [0:1] = '{s, 8'h00};\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "xxxxxxxx");
}

}  // namespace
