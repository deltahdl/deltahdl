#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(ArrayLiteralSynthesis, ConstantArrayInitSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] arr [0:1];\n"
      "  assign arr[0] = 8'hAA;\n"
      "  assign arr[1] = 8'hBB;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(ArrayLiteralSynthesis, ReplicationInitSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] arr [0:2];\n"
      "  assign arr[0] = 8'hFF;\n"
      "  assign arr[1] = 8'hFF;\n"
      "  assign arr[2] = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
