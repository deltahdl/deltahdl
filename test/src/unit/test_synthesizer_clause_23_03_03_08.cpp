
#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

namespace {

// --- R1: The sign attribute shall not cross hierarchy ---

TEST(SignedValuesViaPortsSynthesis,
     SignedToUnsignedPortConnectionSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top(input logic signed [7:0] x, output logic [7:0] y);\n"
      "  child c1(.a(x), .b(y));\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(SignedValuesViaPortsSynthesis,
     UnsignedToSignedPortConnectionSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module child(input logic signed [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top(input logic [7:0] x, output logic [7:0] y);\n"
      "  child c1(.a(x), .b(y));\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(SignedValuesViaPortsSynthesis,
     BothSidesSignedPortConnectionSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module child(input logic signed [7:0] a,\n"
      "             output logic signed [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top(input logic signed [7:0] x,\n"
      "           output logic signed [7:0] y);\n"
      "  child c1(.a(x), .b(y));\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
