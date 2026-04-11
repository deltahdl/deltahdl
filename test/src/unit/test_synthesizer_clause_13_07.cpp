#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(TaskFunctionNameSynth, ForwardFunctionReferenceInContinuousAssign) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m(input logic [7:0] a, output logic [7:0] y);\n"
      "  assign y = double_it(a);\n"
      "  function logic [7:0] double_it(input logic [7:0] v);\n"
      "    return v * 8'd2;\n"
      "  endfunction\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 8);
  EXPECT_EQ(aig->outputs.size(), 8);
}

}  // namespace
