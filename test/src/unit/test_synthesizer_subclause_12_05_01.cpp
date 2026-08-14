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

// The test fails on a synthesizer that answers `AigGraph::kConstTrue` at bit 0
// of `y`, which is what this module lowers to today. §12.5.1 makes only `z` and
// `?` don't-care under `casez`, so bit 64 of the pattern is compared rather
// than ignored, and `SynthLower::MapPorts` in src/synthesizer/synth_lower.cpp
// resizes an undriven variable's bits to `AigGraph::kConstFalse`, so the
// constant-zero `sel` must not match a pattern with that bit set.
// `SetDigitValueBits` in src/synthesizer/synth_pattern.cpp stops at bit 64, so
// the pattern reads as all zeros, the case item matches, and `y` carries
// `AigGraph::kConstTrue`.
//
// The case names `aig->outputs[0]` rather than driving the netlist with
// `EvalAigOutputs`, because `sel` is a variable and not a port, so the netlist
// has no input to drive and its one output bit is an exact literal.
// `EvalAigOutputs` in lib/cpp/test_helpers/helpers_aig_eval.h packs outputs
// into a `uint64_t`, so it cannot describe a netlist with more than 64 output
// bits either.
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

// The test fails on a lowering that reads a case item's pattern out of the
// per-digit decoding whatever base the pattern was written with. A decimal
// literal writes no per-digit bits, so such a lowering compares the selector
// against zero rather than against the value: `4'd3` selects the item at
// `sel == 0` and not at `sel == 3`. §12.5.1 rules that under casez only a z or
// a ? digit is don't-care, and a decimal literal holding neither is compared
// whole, which is the §11.4.5 comparison of the selector against its value.
// The cases above are written with a binary base, so each of their digits
// carries its own bit and none of them reaches this.
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

}  // namespace
