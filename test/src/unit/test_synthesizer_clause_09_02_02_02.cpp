// §9.2.2.2: Combinational logic always_comb procedure

#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(SynthLower, AlwaysCombIfElse) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input sel, input a, input b, output reg y);\n"
                   "  always_comb begin\n"
                   "    if (sel) y = a;\n"
                   "    else y = b;\n"
                   "  end\n"
                   "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 3);
  EXPECT_EQ(aig->outputs.size(), 1);
}

}  // namespace
