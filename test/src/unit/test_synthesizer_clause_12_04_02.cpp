#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(QualifiedIfSynth, UniqueIfSynthesizes) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input [1:0] sel, input a, input b, input c,\n"
                   "         output reg y);\n"
                   "  always_comb begin\n"
                   "    unique if (sel == 2'd0) y = a;\n"
                   "    else if (sel == 2'd1) y = b;\n"
                   "    else y = c;\n"
                   "  end\n"
                   "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs.size(), 1);
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
