#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(ParameterizedSubroutineSynthesis, StaticFunctionCallSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "virtual class C#(parameter W = 8);\n"
      "  static function logic [W-1:0] identity(\n"
      "      input logic [W-1:0] x);\n"
      "    return x;\n"
      "  endfunction\n"
      "endclass\n"
      "module m(input logic [7:0] d, output logic [7:0] q);\n"
      "  assign q = C#(8)::identity(d);\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(ParameterizedSubroutineSynthesis, DifferentSpecializationsSynthesize) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "virtual class C#(parameter W = 8);\n"
      "  static function logic [W-1:0] identity(\n"
      "      input logic [W-1:0] x);\n"
      "    return x;\n"
      "  endfunction\n"
      "endclass\n"
      "module m(input logic [3:0] a, input logic [7:0] b,\n"
      "         output logic [3:0] x, output logic [7:0] y);\n"
      "  assign x = C#(4)::identity(a);\n"
      "  assign y = C#(8)::identity(b);\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
