#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
#include "helpers_synth_input_sweep.h"
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

// §5.7.1: the digits of a decimal literal form its value at the width its size
// constant states, so `81'd1208925819614629174706177` (2^80 + 1) writes bit 80
// as well as bit 0 and nothing between. Expr::int_val holds the value's low 64
// bits alone, and `SynthLower::LowerLiteralBit` read a decimal literal from
// it, answering `AigGraph::kConstFalse` at bit 80. The case names the outputs
// rather than driving the netlist with `EvalAigOutputs`, which packs outputs
// into a `uint64_t` and cannot describe 81 output bits.
TEST(IntegerLiteralSynthesis, WideDecimalLiteralWritesBitEighty) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(output logic [80:0] y);\n"
                           "  assign y = 81'd1208925819614629174706177;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  ASSERT_EQ(aig->outputs.size(), 81u);
  EXPECT_EQ(aig->outputs[80], AigGraph::kConstTrue);
  EXPECT_EQ(aig->outputs[40], AigGraph::kConstFalse);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstTrue);
}

// §5.7.1's first form, a simple decimal number, is folded from its digits the
// same way: the unsized 1180591620717411303424 (2^70) writes bit 70 alone.
TEST(IntegerLiteralSynthesis, UnsizedWideDecimalLiteralWritesBitSeventy) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(output logic [71:0] y);\n"
                           "  assign y = 1180591620717411303424;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  ASSERT_EQ(aig->outputs.size(), 72u);
  EXPECT_EQ(aig->outputs[70], AigGraph::kConstTrue);
  EXPECT_EQ(aig->outputs[69], AigGraph::kConstFalse);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstFalse);
}

// The netlist `src` lowers to, or null where elaboration or lowering fails.
// The cases below drive a constant literal into an output port, so the netlist
// has no input and each output bit is an exact literal.
static const AigGraph* LowerSrc(SynthFixture& f, const std::string& src) {
  const auto* mod = ElaborateSrc(f, src);
  if (mod == nullptr) return nullptr;
  SynthLower synth(f.arena, f.diag);
  return synth.Lower(mod);
}

// §5.7.1: an unsigned number wider than the size constant is truncated from
// the left, so `8'hFFF` is the eight-bit 8'hFF and a 12-bit `y` reads 0x0FF.
// `PatternBitValue` in src/synthesizer/synth_pattern.cpp answered whatever the
// digits wrote, so bits 8 to 11 of `y` read the dropped digit's ones and `y`
// read 0xFFF.
TEST(IntegerLiteralSynthesis, SizedHexLiteralIsTruncatedFromTheLeftToItsSize) {
  SynthFixture f;
  const auto* aig = LowerSrc(f,
                             "module m(output logic [11:0] y);\n"
                             "  assign y = 8'hFFF;\n"
                             "endmodule\n");
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(EvalAigOutputs(*aig, 0), 0x0FFu);
}

// §5.7.1's truncation reaches a based decimal as well: `8'd300` is 300 modulo
// 256, which is 44, and bit 8 of `y` is clear.
TEST(IntegerLiteralSynthesis,
     SizedDecimalLiteralIsTruncatedFromTheLeftToItsSize) {
  SynthFixture f;
  const auto* aig = LowerSrc(f,
                             "module m(output logic [11:0] y);\n"
                             "  assign y = 8'd300;\n"
                             "endmodule\n");
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(EvalAigOutputs(*aig, 0), 44u);
}

// §5.7.1: `80'd1208925819614629174706177` (2^80 + 1) is 81 bits wide and its
// size constant is 80, so bit 80 is truncated away and bit 0 alone stands;
// a 96-bit `y` reads bit 80 clear. The case names the outputs rather than
// driving the netlist with `EvalAigOutputs`, which packs outputs into a
// `uint64_t` and cannot describe 96 output bits.
TEST(IntegerLiteralSynthesis, WideDecimalLiteralDropsBitAtItsSize) {
  SynthFixture f;
  const auto* aig = LowerSrc(f,
                             "module m(output logic [95:0] y);\n"
                             "  assign y = 80'd1208925819614629174706177;\n"
                             "endmodule\n");
  ASSERT_NE(aig, nullptr);
  ASSERT_EQ(aig->outputs.size(), 96u);
  EXPECT_EQ(aig->outputs[80], AigGraph::kConstFalse);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstTrue);
}

// §5.7.1 truncates a don't-care digit the same way: `4'b?0000` is five digits
// under a size constant of 4, so the `?` is dropped and the pattern is
// `4'b0000`, which §12.5.1 matches at `sel == 0` alone once zero-extended to
// the eight-bit selector. A pattern keeping the dropped digit's don't-care at
// bit 4 would match `sel == 8'h10` as well.
TEST(IntegerLiteralSynthesis, CasezPatternDigitAboveItsSizeIsTruncated) {
  ExpectInputSweep(
      "module m(input [7:0] sel, output logic y);\n"
      "  always_comb begin\n"
      "    casez (sel)\n"
      "      4'b?0000: y = 1'b1;\n"
      "      default: y = 1'b0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      32, [](uint64_t sel) { return sel == 0 ? uint64_t{1} : uint64_t{0}; });
}

}  // namespace
