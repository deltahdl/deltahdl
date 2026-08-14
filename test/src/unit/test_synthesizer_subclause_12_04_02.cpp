#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
#include "helpers_synth_select.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(QualifiedIfSynth, UniqueIfSynthesizes) {
  ExpectSelChoosesAmongThreeSources(
      "module m(input [1:0] sel, input a, input b, input c,\n"
      "         output reg y);\n"
      "  always_comb begin\n"
      "    unique if (sel == 2'd0) y = a;\n"
      "    else if (sel == 2'd1) y = b;\n"
      "    else y = c;\n"
      "  end\n"
      "endmodule");
}

TEST(QualifiedIfSynth, Unique0IfSynthesizes) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input [1:0] sel, input [7:0] a, input [7:0] b,\n"
                   "         output reg [7:0] y);\n"
                   "  always_comb begin\n"
                   "    y = 8'd0;\n"
                   "    unique0 if (sel == 2'd0) y = a;\n"
                   "    else if (sel == 2'd1) y = b;\n"
                   "  end\n"
                   "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs.size(), 8);
  // The sweep fails on the netlist this module lowered to before `sel == 2'd0`
  // and `sel == 2'd1` had a lowering: both comparisons answered
  // `AigGraph::kConstFalse`, and `AigGraph::AddMux` with a constant-false
  // select hands back the else literal and builds no node, so every bit of `y`
  // carried the `8'd0` the body assigns first and `a` and `b` reached nothing.
  // The output count above never noticed, because the port list fixes that
  // count whatever the netlist computes.
  //
  // `SynthLower::MapPorts` walks `mod->ports` in declaration order and
  // allocates one AIG input per bit, low bit first, so `sel` takes bits 0 and 1
  // of the word, `a` takes bits 2 to 9 and `b` takes bits 10 to 17. Output j
  // lands in bit j, so the whole of `y` reads back as one byte.
  //
  // Four pairs of eight-bit values stand for all 65536, because the three
  // sources this body selects between are told apart by any pair whose members
  // are nonzero and differ from each other: nonzero separates a selected source
  // from the `8'd0` fallback, and the difference separates `a` from `b`. 0xA5
  // and 0x5A are complements, 0xFF and 0x0F differ in the high nibble alone,
  // 0x01 and 0x80 are the two ends of the byte, and 0x3C and 0xC3 are
  // complements straddling the nibble boundary, so a netlist that reverses,
  // shifts or truncates the bits of a source disagrees on at least one pair.
  static const uint64_t kValuePairs[][2] = {
      {0xA5, 0x5A}, {0xFF, 0x0F}, {0x01, 0x80}, {0x3C, 0xC3}};
  for (uint64_t sel = 0; sel < 4; ++sel) {
    for (const auto& pair : kValuePairs) {
      uint64_t a = pair[0];
      uint64_t b = pair[1];
      uint64_t expected = sel == 0 ? a : (sel == 1 ? b : uint64_t{0});
      EXPECT_EQ(EvalAigOutputs(*aig, sel | (a << 2) | (b << 10)), expected)
          << "sel = " << sel << ", a = " << a << ", b = " << b;
    }
  }
}

TEST(QualifiedIfSynth, PriorityIfSynthesizes) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input a, input b, input x, input y, input z,\n"
                   "         output reg o);\n"
                   "  always_comb begin\n"
                   "    priority if (a) o = x;\n"
                   "    else if (b) o = y;\n"
                   "    else o = z;\n"
                   "  end\n"
                   "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs.size(), 1);
}

}  // namespace
