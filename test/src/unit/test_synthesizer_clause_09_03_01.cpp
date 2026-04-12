#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
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

}  // namespace
