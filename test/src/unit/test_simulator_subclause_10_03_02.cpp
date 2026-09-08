#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ContAssignStatementSim, NetDrivenByConstant) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [7:0] a;\n"
      "  assign a = 8'hAB;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(ContAssignStatementSim, MultipleContinuousAssignments) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial a = 8'd10;\n"
      "  assign b = a + 8'd1;\n"
      "  assign c = a + 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 11u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 12u);
}

TEST(ContAssignStatementSim, ContinuousAssignChain) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial a = 8'd7;\n"
      "  assign b = a;\n"
      "  assign c = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 7u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 7u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 7u);
}

TEST(ContAssignStatementSim, ReEvaluatesWhenOperandChanges) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  assign b = a;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    #1;\n"
      "    a = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // The continuous assignment statement re-evaluates its RHS on every change of
  // an operand, so b tracks the latest value driven onto a rather than freezing
  // at the value present when simulation started.
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 42u);
}

TEST(ContAssignStatementSim, ContAssignOnVectorVariable) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] wide;\n"
      "  assign wide = 16'hCAFE;\n"
      "endmodule\n",
      f, "wide");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEu);
}

// A continuous assignment may target a concatenation on the left-hand side —
// the form §10.3.2 uses to drive several nets that could not be assigned in a
// single net declaration. Each element receives its own most-significant-first
// slice of the whole right-hand value: for {hi, lo} = 8'hAB, hi takes the top
// nibble and lo the bottom nibble.
TEST(ContAssignStatementSim, ContAssignToConcatenationLhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] hi, lo;\n"
      "  assign {hi, lo} = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("hi")->value.ToUint64(), 0xAu);
  EXPECT_EQ(f.ctx.FindVariable("lo")->value.ToUint64(), 0xBu);
}

// The driven net of a continuous assignment can inherit an implicit declaration
// (§6.10) rather than being declared explicitly. Built from that real form —
// an undeclared left-hand name — the implicit net is created, driven, and
// carries the assigned value at the end of the run.
TEST(ContAssignStatementSim, ContAssignDrivesImplicitlyDeclaredNet) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §10.3.2: "Nets can be driven by multiple continuous assignments or by a
// mixture of primitive outputs, module outputs, and continuous assignments." A
// continuous assignment into a select of a net is one of those drivers, so the
// net has a driver to resolve rather than a value written into it behind
// resolution's back. A whole-identifier target cannot fail this.
TEST(ContAssignStatementSim, SelectTargetRegistersADriverOnTheNet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [1:0] w;\n"
      "  assign w[0] = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->drivers.size(), 1u);
}

// The driver drives only the bits the select names, and high impedance
// everywhere else, so §28.12 decides the rest of the net from its other
// sources. §6.6.5 gives a tri0 net "a continuous 0 of pull strength" wherever
// nothing overrides it, and that is what the undriven nibble resolves to: the
// low nibble is the assignment's strong 1 and the high nibble the net's own
// pull 0. Written into storage rather than resolved, the net would report the
// undriven answer for all eight bits.
TEST(ContAssignStatementSim, SelectTargetDrivesOnlyTheBitsItNames) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  tri0 [7:0] w;\n"
      "  assign w[3:0] = 4'hF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->BitStrength(0).s1_hi, Strength::kStrong);
  EXPECT_EQ(w->BitStrength(0).s0_hi, Strength::kHighz);
  EXPECT_EQ(w->BitStrength(4).s0_hi, Strength::kPull);
  EXPECT_EQ(w->BitStrength(4).s1_hi, Strength::kHighz);
}

// Two assignments into overlapping selects of one net are two drivers, and
// §28.12 combines them where they overlap: bits 1 and 2 are driven 1 by one and
// 0 by the other at the same strength, which resolves to x, while the bits only
// one of them names keep that one's value. A direct write into storage would
// leave whichever assignment ran last standing over the whole overlap.
TEST(ContAssignStatementSim, OverlappingSelectTargetsResolveAgainstEachOther) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [3:0] w;\n"
      "  assign w[2:0] = 3'b111;\n"
      "  assign w[3:1] = 3'b000;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->drivers.size(), 2u);
  EXPECT_EQ(w->resolved->value.ToString(), "0xx1");
}

// §11.5.1: "Part-selects that are partially out of range shall, when read,
// return x for the bits that are out of range and shall, when written, only
// affect the bits that are in range." The indexed form `a[1 -: 4]` descends
// from its base, so on `[7:0] a` it names indices 1, 0, -1 and -2, and the two
// of those inside the net are the select's own most significant end. They take
// the value's most significant end with them: a[1] takes 4'b1101's bit 3 and
// a[0] its bit 2, both 1. §6.6.5 gives a tri0 a continuous pull 0 wherever no
// driver reaches, which is the other six bits, so `a` reads 8'h03.
//
// `4'b1101` is what lets this case fail. A driver that kept the value's least
// significant bits and simply narrowed the window it drove them into would put
// bit 1's 0 on a[1] and bit 0's 1 on a[0], reading 8'h01. The select-target
// cases above cannot separate the two: 4'hF and 3'b111 are one bit repeated,
// so every way of choosing which bits of the value to take gives them the same
// answer, and every select in them lies wholly inside its net besides.
TEST(ContAssignStatementSim, SelectTargetRunningOffLowEndDrivesItsOwnHighBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  tri0 [7:0] a;\n"
      "  assign a[1 -: 4] = 4'b1101;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* a = f.ctx.FindNet("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->resolved->value.ToUint64() & 0xFFu, 0x03u);
}

// The same select on a plain wire, which is the other half of §11.5.1's
// sentence: the bits out of range are not this driver's, and on a net with no
// other source they stay z. The two bits in range hold the value's bits 3 and
// 2, so the resolution reads zzzzzz11.
//
// The tri0 case above cannot say this. Its pull answers 0 for a bit no driver
// reaches, ToUint64 reads x and z alike as 0, and so a driver that also drove
// the six other bits to 0, or that drove any of them to x by conflicting with
// itself over a clamped index, reads 8'h03 there just the same. Here each of
// those shows as its own character in the string, and the assertion is on
// which bits this one driver claims rather than only on what two of them hold.
TEST(ContAssignStatementSim,
     SelectTargetRunningOffLowEndLeavesTheOtherBitsUndriven) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [7:0] a;\n"
      "  assign a[1 -: 4] = 4'b1101;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* a = f.ctx.FindNet("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->resolved->value.ToString(), "zzzzzz11");
}

// The companion overhanging the top, which the same sentence governs and which
// no fix to the low end may disturb. `a[9:6]` on `[7:0] a` names indices 9, 8,
// 7 and 6; the two in range are 7 and 6, and they are the select's own least
// significant end, so they take the value's bits 1 and 0. `4'b1101` puts 0 on
// a[7] and 1 on a[6], and with §6.6.5's pull 0 under the rest `a` reads 8'h40.
//
// This passes today, and it is here to catch the correction made in the wrong
// direction. A driver that shifted the value by the count of indices running
// off the *high* end rather than the low would take bits 3 and 2 here and read
// 8'hC0. ExpressionSim.PartSelectRunningOffHighEndStillTakesItsLowBits in
// test_simulator_subclause_11_05_01a.cpp holds this same line for the
// procedural writer; a continuous assignment reaches the net through a driver
// and a resolution instead, and that path needs its own case.
TEST(ContAssignStatementSim,
     SelectTargetRunningOffHighEndStillTakesItsLowBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  tri0 [7:0] a;\n"
      "  assign a[9:6] = 4'b1101;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* a = f.ctx.FindNet("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->resolved->value.ToUint64() & 0xFFu, 0x40u);
}

// A select may hang off both ends at once, and then both of §11.5.1's answers
// are in play together. `a[9 -: 12]` on `[7:0] a` is `a[9:-2]`, twelve indices
// of which the eight in the net are in range: the window is clamped at the top
// as well as at the bottom, so its width is the net's eight rather than the
// select's declared twelve, while its source offset is still the two indices
// below the net. The bits that land are the value's [9:2]. `12'hABC` is
// 1010_1011_1100, whose bits 9 through 2 are 1010_1111, so `a` reads 8'hAF.
//
// A driver that carried the source offset but sized the deposit from the
// select's declared width would answer here and nowhere else in this file: the
// three cases above are each clamped at one end only, where the declared width
// and the driven width agree once the offset is applied.
// ExpressionSim.PartSelectRunningOffBothEndsWritesItsMiddleBits in
// test_simulator_subclause_11_05_01a.cpp holds the same line for the
// procedural writer.
TEST(ContAssignStatementSim, SelectTargetRunningOffBothEndsLandsItsMiddleBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  tri0 [7:0] a;\n"
      "  assign a[9 -: 12] = 12'hABC;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* a = f.ctx.FindNet("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->resolved->value.ToUint64() & 0xFFu, 0xAFu);
}

}  // namespace
