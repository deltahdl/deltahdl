#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
#include "helpers_synth_assign.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

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
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "a << 3"), 1,
                    [](uint64_t a, uint64_t) { return (a << 3) & 0xFU; });
}

TEST(OperatorSynthesis, TripleCharOperatorSynthesizes) {
  ExpectAssignSweep(ModuleAssigning("input [3:0] a", "a <<< 3"), 1,
                    [](uint64_t a, uint64_t) { return (a << 3) & 0xFU; });
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
