#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(IntegerLiteralSynthesis, UnsizedDecimalSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] a, result;\n"
                           "  assign result = 42;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, SizedHexSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] result;\n"
                           "  assign result = 8'hFF;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, SizedBinarySynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [3:0] result;\n"
                           "  assign result = 4'b1010;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, SizedOctalSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] result;\n"
                           "  assign result = 8'o77;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, SizedDecimalSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] result;\n"
                           "  assign result = 8'd200;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, UnbasedUnsizedOneSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] result;\n"
                           "  assign result = '1;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, UnbasedUnsizedZeroSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] result;\n"
                           "  assign result = '0;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, UnderscoreSeparatorSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [31:0] result;\n"
                           "  assign result = 32'hDEAD_BEEF;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, SignedLiteralSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] result;\n"
                           "  assign result = 8'sd99;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

// The test fails on a synthesizer that answers `AigGraph::kConstTrue` at bit 64
// of `y`, which is what `assign y = 128'd5;` lowers to today. §5.7.1 rules that
// "If the size of the unsigned number is smaller than the size specified for
// the literal constant, the unsigned number shall be padded to the left with
// zeros", so every bit of `128'd5` above bit 2 is zero and bit 64 of `y` is
// `AigGraph::kConstFalse`. `SynthLower::LowerExprBit` in
// src/synthesizer/synth_lower.cpp answers a literal's bit as
// `((expr->int_val >> bit) & 1u)`, and `Expr::int_val` in src/parser/ast_expr.h
// is a `uint64_t`. Shifting a 64-bit value by 64 or more is undefined in C++,
// and on the machines this is built for the shift count is taken modulo 64, so
// bit 64 of a literal answers bit 0 of its value.
//
// The value is 5 rather than an even number deliberately. Bit 0 of 5 is one, so
// the wrapped shift answers `AigGraph::kConstTrue` at bit 64 where §5.7.1 owes
// `AigGraph::kConstFalse`. A literal whose bit 0 is zero would be answered
// correctly by the wrap and would pass whether the fix exists or not.
//
// The case names `aig->outputs[64]` rather than driving the netlist with
// `EvalAigOutputs`, which packs outputs into a `uint64_t` in
// lib/cpp/test_helpers/helpers_aig_eval.h and so cannot describe a netlist with
// more than 64 output bits. A bit driven by a literal carries an exact literal,
// `AigGraph::kConstFalse` or `AigGraph::kConstTrue`, so naming it states the
// value rather than the gates.
TEST(IntegerLiteralSynthesis,
     SizedLiteralZeroFillsBitSixtyFourOfAContinuousAssignTarget) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(output logic [127:0] y);\n"
                           "  assign y = 128'd5;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs[64], AigGraph::kConstFalse);
}

// The test fails on a fix that reaches the continuous assignment and leaves a
// procedural one answering `AigGraph::kConstTrue` at bit 64, which the case
// above passes. `SynthLower::LowerContAssign` and `SynthLower::LowerAssignStmt`
// in src/synthesizer/synth_lower.cpp each walk the bits of their own target, so
// the two cases reach `SynthLower::LowerExprBit` from different loops and one
// leaves the other path uncovered.
//
// §5.7.1 owes `AigGraph::kConstFalse` at bit 64 here for the reason it owes it
// above: `128'd5` is padded to the left with zeros, so every bit of it above
// bit 2 is zero. The value is 5 rather than an even number so that the wrapped
// shift `((expr->int_val >> bit) & 1u)` answers `AigGraph::kConstTrue` at bit
// 64, which a literal whose bit 0 is zero would not do.
//
// The case names `aig->outputs[64]` rather than driving the netlist with
// `EvalAigOutputs`, which packs outputs into a `uint64_t` and cannot describe
// this netlist's 128 output bits.
TEST(IntegerLiteralSynthesis,
     SizedLiteralZeroFillsBitSixtyFourOfAProceduralTarget) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(output logic [127:0] y);\n"
                           "  always_comb y = 128'd5;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs[64], AigGraph::kConstFalse);
}

}  // namespace
