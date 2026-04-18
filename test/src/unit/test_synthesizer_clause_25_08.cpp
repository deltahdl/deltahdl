#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

namespace {

TEST(ParameterizedInterfaceSynthesis, DefaultParameterSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n"
      "module top;\n"
      "  ifc u0();\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(ParameterizedInterfaceSynthesis, PositionalOverrideSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n"
      "module top;\n"
      "  ifc #(16) u0();\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(ParameterizedInterfaceSynthesis, NamedOverrideSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n"
      "module top;\n"
      "  ifc #(.WIDTH(32)) u0();\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(ParameterizedInterfaceSynthesis, MultipleInstancesWithDifferentOverrides) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n"
      "module top;\n"
      "  ifc #(.WIDTH(4)) narrow();\n"
      "  ifc #(.WIDTH(16)) wide();\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
