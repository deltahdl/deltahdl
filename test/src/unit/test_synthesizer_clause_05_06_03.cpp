#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(SystemNameSynthesis, SystemFunctionInAssignSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [31:0] w;\n"
      "  assign w = $clog2(16);\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(SystemNameSynthesis, SystemFunctionInExpressionSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] a, result;\n"
      "  assign result = a + $clog2(32);\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(SystemNameSynthesis, SystemFunctionWithDataTypeArgSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [31:0] w;\n"
      "  assign w = $bits(logic [7:0]);\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
