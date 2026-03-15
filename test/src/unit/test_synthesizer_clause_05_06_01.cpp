#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(EscapedIdentifierSynthesis, EscapedIdentifierSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] \\bus+a , result;\n"
      "  assign result = \\bus+a ;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(EscapedIdentifierSynthesis, EscapedIdentifierSpecialCharsSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] \\***sig*** , result;\n"
      "  assign result = \\***sig*** ;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(EscapedIdentifierSynthesis, EscapedKeywordSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] \\module , result;\n"
      "  assign result = \\module ;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(EscapedIdentifierSynthesis, MultipleEscapedIdentifiersSynthesize) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] \\a+b , \\c-d , result;\n"
      "  assign result = \\a+b + \\c-d ;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(EscapedIdentifierSynthesis, EscapedIdentMatchesSimpleIdentSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] cpu3, result;\n"
      "  assign result = \\cpu3 ;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
