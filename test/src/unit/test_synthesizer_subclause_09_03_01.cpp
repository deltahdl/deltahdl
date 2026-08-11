#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(SequentialBlockSynthesis, SeqBlockInAlwaysCombSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic a, b, c;\n"
                           "  always_comb begin\n"
                           "    b = a;\n"
                           "    c = b;\n"
                           "  end\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(SequentialBlockSynthesis, SeqBlockInAlwaysFfSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic clk;\n"
                           "  logic [7:0] q, d;\n"
                           "  always_ff @(posedge clk) begin\n"
                           "    q <= d;\n"
                           "  end\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(SequentialBlockSynthesis, EmptySeqBlockInAlwaysCombSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic a, b;\n"
                           "  always_comb begin\n"
                           "    a = b;\n"
                           "    begin\n"
                           "    end\n"
                           "  end\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

// §9.3.1: the statements of a sequential block execute in the order they are
// written, so every one of them contributes to what the block leaves behind.
// Naming the literal each output carries is what makes that testable. A
// synthesizer that walks the block and quietly skips a statement it does not
// recognise still returns a graph, so `ASSERT_NE(aig, nullptr)` above passes
// over a netlist that has lost half the design; only an assertion about the
// value an output ends up with can tell the two apart. `y` is the one that
// catches it, since it is assigned by the second statement of the block.
TEST(SequentialBlockSynthesis,
     LoweredAssignmentSurvivesEveryStatementInTheBlock) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, input b,\n"
                           "         output logic x, output logic y);\n"
                           "  always_comb begin\n"
                           "    x = a;\n"
                           "    y = b;\n"
                           "  end\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  ASSERT_EQ(aig->inputs.size(), 2u);
  ASSERT_EQ(aig->outputs.size(), 2u);
  EXPECT_EQ(aig->outputs[0], AigLit(aig->inputs[0], false));
  EXPECT_EQ(aig->outputs[1], AigLit(aig->inputs[1], false));
}

}  // namespace
