
#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

namespace {

// --- Rule (a): Struct member select synthesizes ---

TEST(DottedNameSynthesis, StructMemberSelectSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module t(input logic [15:0] s, output logic [7:0] y);\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  assign p = s;\n"
      "  assign y = p.hi;\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(DottedNameSynthesis, NestedStructMemberSelectSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module t(input logic [15:0] s, output logic [7:0] y);\n"
      "  typedef struct packed { logic [7:0] x; } inner_t;\n"
      "  typedef struct packed { inner_t sub; logic [7:0] pad; } outer_t;\n"
      "  outer_t o;\n"
      "  assign o = s;\n"
      "  assign y = o.sub.x;\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
