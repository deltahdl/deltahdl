#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(IntegerLiteralSynthesis, UnsizedDecimalSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] a, result;\n"
      "  assign result = 42;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, SizedHexSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] result;\n"
      "  assign result = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, SizedBinarySynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [3:0] result;\n"
      "  assign result = 4'b1010;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, SizedOctalSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] result;\n"
      "  assign result = 8'o77;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, SizedDecimalSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] result;\n"
      "  assign result = 8'd200;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, UnbasedUnsizedOneSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] result;\n"
      "  assign result = '1;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, UnbasedUnsizedZeroSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] result;\n"
      "  assign result = '0;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, UnderscoreSeparatorSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [31:0] result;\n"
      "  assign result = 32'hDEAD_BEEF;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IntegerLiteralSynthesis, SignedLiteralSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] result;\n"
      "  assign result = 8'sd99;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
