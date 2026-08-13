#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// The test fails on a netlist whose `a` is not the sum of `b` and `c`. The
// assertion it had before, that `SynthLower::Lower` answered a graph, holds
// over a netlist in which every bit of `a` is a constant zero, and that is what
// a `SynthLower::LowerBinaryBit` with no arm for `+` builds. This case is the
// one §5.5 names for the lexing of a one-character operator and the `+` is the
// operator it lexes, and no case under test/src/unit/ said what a `+` in a
// continuous assignment leaves in the netlist: every other synthesizer case
// holding one asserts that the graph is non-null and nothing more.
//
// The operands are ports rather than the internal variables this case declared,
// because `EvalAigOutputs` reaches a netlist only through the inputs
// `SynthLower::MapPorts` allocates and the outputs
// `SynthLower::RegisterOutputs` registers, and a module with no ports has
// neither. Both walk the ports in declaration order, least significant bit
// first, so input bit i carries `b[i]`, input bit i + 4 carries `c[i]`, and
// output bit i carries `a[i]`.
//
// The sweep drives all 256 pairs of four-bit operands rather than the 65536
// pairs eight-bit operands would take. Four bits is a carry chain long enough
// that a netlist propagating no carry disagrees, `4'hF + 4'h1` wraps at the top
// of it, and a regression reports 256 failures rather than 65536. Hand-picked
// pairs are what the width may not be narrowed to: an addition that drops the
// carry agrees with a correct one at every pair whose bits do not overlap.
TEST(OperatorSynthesis, SingleCharOperatorSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input [3:0] b, input [3:0] c,\n"
                           "         output logic [3:0] a);\n"
                           "  assign a = b + c;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  for (uint64_t b = 0; b < 16; ++b) {
    for (uint64_t c = 0; c < 16; ++c) {
      EXPECT_EQ(EvalAigOutputs(*aig, b | (c << 4)), (b + c) & 0xFU)
          << "b = " << b << ", c = " << c;
    }
  }
}

TEST(OperatorSynthesis, DoubleCharOperatorSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] a, b;\n"
                           "  assign a = b << 1;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(OperatorSynthesis, TripleCharOperatorSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] a, b;\n"
                           "  assign a = b <<< 1;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(OperatorSynthesis, UnaryOperatorSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] a, b;\n"
                           "  assign a = ~b;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(OperatorSynthesis, BinaryOperatorSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] a, b, c;\n"
                           "  assign a = b & c;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(OperatorSynthesis, ConditionalOperatorSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic sel;\n"
                           "  logic [7:0] a, b, c;\n"
                           "  assign a = sel ? b : c;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(OperatorSynthesis, MixedOperatorsSynthesize) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] a, b, c, d;\n"
                           "  assign a = (b + c) & ~d;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
