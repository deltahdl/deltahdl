#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_synth_input_sweep.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(CasezStatementSynth, AlwaysCombCasezStmt) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input logic [1:0] sel, output logic [1:0] y);\n"
                   "  always_comb begin\n"
                   "    casez (sel)\n"
                   "      2'b1?: y = 2'b01;\n"
                   "      2'b01: y = 2'b10;\n"
                   "      default: y = 2'b00;\n"
                   "    endcase\n"
                   "  end\n"
                   "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 2);
  EXPECT_EQ(aig->outputs.size(), 2);
}

TEST(CasexStatementSynth, AlwaysCombCasexStmt) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input logic [1:0] sel, output logic [1:0] y);\n"
                   "  always_comb begin\n"
                   "    casex (sel)\n"
                   "      2'b1x: y = 2'b01;\n"
                   "      2'b01: y = 2'b10;\n"
                   "      default: y = 2'b00;\n"
                   "    endcase\n"
                   "  end\n"
                   "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 2);
  EXPECT_EQ(aig->outputs.size(), 2);
}

TEST(CasezStatementSynth,
     CasezPatternBitAboveSixtyThreeIsMatchedRatherThanIgnored) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(output logic y);\n"
                           "  logic [70:0] sel;\n"
                           "  always_comb begin\n"
                           "    casez (sel)\n"
                           "      71'h1_0000_0000_0000_0000: y = 1'b1;\n"
                           "      default: y = 1'b0;\n"
                           "    endcase\n"
                           "  end\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstFalse);
}

TEST(CasezStatementSynth, CasezAgainstADecimalPatternComparesItsValue) {
  ExpectInputSweep(
      "module m(input [3:0] sel, output logic y);\n"
      "  always_comb begin\n"
      "    casez (sel)\n"
      "      4'd3: y = 1'b1;\n"
      "      default: y = 1'b0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      16, [](uint64_t sel) { return sel == 3 ? uint64_t{1} : uint64_t{0}; });
}

TEST(CasezStatementSynth, FirstMatchingItemWins) {
  ExpectInputSweep(
      "module m(input logic [1:0] sel, output logic [1:0] y);\n"
      "  always_comb begin\n"
      "    casez (sel)\n"
      "      2'b1?: y = 2'd1;\n"
      "      2'b11: y = 2'd2;\n"
      "      default: y = 2'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      4, [](uint64_t sel) { return sel >= 2 ? uint64_t{1} : uint64_t{0}; });
}

}  // namespace
