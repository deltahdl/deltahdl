
#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

namespace {

TEST(NamedPortSynthesis, NamedPortConnectionSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module child(input logic a, output logic y);\n"
      "  assign y = ~a;\n"
      "endmodule\n"
      "module top(input logic a, output logic y);\n"
      "  child c1(.a(a), .y(y));\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(NamedPortSynthesis, NamedPortEmptyConnectionSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module child(input logic a, output logic b, output logic c);\n"
      "  assign b = a;\n"
      "  assign c = ~a;\n"
      "endmodule\n"
      "module top(input logic a, output logic y);\n"
      "  child c1(.a(a), .b(y), .c());\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(NamedPortSynthesis, ReversedNamedPortOrderSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module child(input logic a, output logic y);\n"
      "  assign y = a;\n"
      "endmodule\n"
      "module top(input logic a, output logic y);\n"
      "  child c1(.y(y), .a(a));\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(NamedPortSynthesis, NamedPortWithExpressionSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module child(input logic a, output logic y);\n"
      "  assign y = a;\n"
      "endmodule\n"
      "module top(input logic a, input logic b, output logic y);\n"
      "  child c1(.a(a & b), .y(y));\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
