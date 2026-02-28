// §7.4.1: Packed arrays

#include <gtest/gtest.h>

#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"
#include "fixture_synthesizer.h"

using namespace delta;

namespace {

TEST(SynthLower, MultiBitPortMapping) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input logic [3:0] a, output logic [3:0] y);\n"
                   "  assign y = a;\n"
                   "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 4);
  EXPECT_EQ(aig->outputs.size(), 4);
}

}  // namespace
