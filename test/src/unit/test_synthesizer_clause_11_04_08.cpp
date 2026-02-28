// §11.4.8: Bitwise operators

#include <gtest/gtest.h>

#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"
#include "fixture_synthesizer.h"

using namespace delta;

namespace {

TEST(SynthLower, MultiBitAndGate) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input logic [1:0] a, input logic [1:0] b,\n"
                   "         output logic [1:0] y);\n"
                   "  assign y = a & b;\n"
                   "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 4);
  EXPECT_EQ(aig->outputs.size(), 2);
}

}  // namespace
