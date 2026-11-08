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
