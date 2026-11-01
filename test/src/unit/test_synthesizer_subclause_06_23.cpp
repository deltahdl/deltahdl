#include <gtest/gtest.h>

#include <array>
#include <cstdint>

#include "elaborator/rtlir.h"
#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// This file covers the type operator §6.23 defines, written as an operand of a
// comparison on the right-hand side of a continuous assignment, which
// `SynthLower::LowerExprBit` in src/synthesizer/synth_lower.cpp has no
// lowering for.

// §6.23 with §6.22.1: a comparison of two type references is a constant, which
// the elaborator folds to the bit it stands for wherever it can type both
// operands, as it can two ports, an operation on them and a written type. The
// netlist carries those bits: a's type, logic [3:0], matches b's and that of
// a + b, and does not match bit [3:0], a 2-state type.
TEST(TypeOperatorSynthesis, FoldedComparisonLowersToTheBitItStandsFor) {
  SynthFixture f;
  const auto* mod = ElaborateSrc(
      f,
      "module m(input [3:0] a, input [3:0] b, output logic [2:0] y);\n"
      "  assign y = {type(a) == type(b), type(a) == type(bit [3:0]),\n"
      "              type(a + b) == type(logic [3:0])};\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs[2], AigGraph::kConstTrue);
  EXPECT_EQ(aig->outputs[1], AigGraph::kConstFalse);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstTrue);
}

// The case fails on a run that answers a netlist for this module. The
// elaborator gives a slice of an unpacked array no type, since the bounds its
// type would match by (§6.22.1(f)) are not ones the standard states, so it
// leaves this comparison unfolded, and each operand of the comparison reaches
// `SynthLower::LowerExprBit` in src/synthesizer/synth_lower.cpp as an
// `ExprKind::kTypeRef`, for which that function builds no node. A design that
// wrote the operator got a netlist contributing constant zero at every bit of
// the expression while the run reported success. §6.23 rules that a type
// reference is compared only with another type reference, which is what the
// source writes, and §11.4.5 makes the comparison the one bit the target
// declares.
TEST(TypeOperatorSynthesis, TypeReferenceIsReportedRatherThanLoweredToZero) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(output logic y);\n"
                   "  logic [3:0] u [4];\n"
                   "  assign y = (type(u[0:1]) == type(u[2:3]));\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the type operator has no lowering", 3, "6.23"));
}

// §6.23 with §6.20.3: each instance of a module binds its own parameters, so
// one comparison written in the module lowers, in each instance's netlist, to
// the bit that instance's types give, in a continuous assignment and in an
// always_comb procedure alike. The first instance elaborated is the one whose
// answers differ from the instance the case reads last.
TEST(TypeOperatorSynthesis, EachInstanceLowersItsOwnComparison) {
  SynthFixture f;
  const auto* top = ElaborateSrc(
      f,
      "module w #(type T = int, int W = 8)(output logic [3:0] y);\n"
      "  T x;\n"
      "  logic [W-1:0] v;\n"
      "  assign y[3:2] = {type(x) == type(int), type(v) == type(logic "
      "[7:0])};\n"
      "  always_comb y[1:0] = {type(x) != type(int), type(v) !== type(logic "
      "[7:0])};\n"
      "endmodule\n"
      "module t; w #(int, 4) d(); w #(byte, 8) c(); endmodule\n");
  ASSERT_NE(top, nullptr);
  ASSERT_EQ(top->children.size(), 2u);
  struct Expected {
    const char* inst;
    std::array<uint32_t, 4> bits;
  };
  for (const Expected& e :
       {Expected{"d",
                 {AigGraph::kConstTrue, AigGraph::kConstFalse,
                  AigGraph::kConstFalse, AigGraph::kConstTrue}},
        Expected{"c",
                 {AigGraph::kConstFalse, AigGraph::kConstTrue,
                  AigGraph::kConstTrue, AigGraph::kConstFalse}}}) {
    SCOPED_TRACE(e.inst);
    const RtlirModule* inst = nullptr;
    for (const auto& child : top->children) {
      if (child.inst_name == e.inst) inst = child.resolved;
    }
    ASSERT_NE(inst, nullptr);
    SynthLower synth(f.arena, f.diag);
    auto* aig = synth.Lower(inst);
    ASSERT_NE(aig, nullptr);
    ASSERT_EQ(aig->outputs.size(), 4u);
    EXPECT_EQ(aig->outputs[0], e.bits[0]);
    EXPECT_EQ(aig->outputs[1], e.bits[1]);
    EXPECT_EQ(aig->outputs[2], e.bits[2]);
    EXPECT_EQ(aig->outputs[3], e.bits[3]);
  }
}

// §27.4: each iteration of a loop generate block declares v with the width its
// genvar gives, and its assignment lowers to the comparison of its own v.
TEST(TypeOperatorSynthesis, EachLoopIterationLowersItsOwnComparison) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(output logic [1:0] y);\n"
                   "  for (genvar i = 0; i < 2; i++) begin : g\n"
                   "    logic [i:0] v;\n"
                   "    assign y[i] = type(v) == type(logic [0:0]);\n"
                   "  end\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  ASSERT_EQ(aig->outputs.size(), 2u);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstTrue);
  EXPECT_EQ(aig->outputs[1], AigGraph::kConstFalse);
}

}  // namespace
