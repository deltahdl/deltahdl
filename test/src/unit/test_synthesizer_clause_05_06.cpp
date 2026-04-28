#include <gtest/gtest.h>

#include <string>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(IdentifierSynthesis, SimpleIdentifierSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] abc_123, result;\n"
      "  assign result = abc_123;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IdentifierSynthesis, IdentifierWithDollarSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] n$657, result;\n"
      "  assign result = n$657;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IdentifierSynthesis, IdentifierStartingWithUnderscoreSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] _bus3, result;\n"
      "  assign result = _bus3;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IdentifierSynthesis, CaseSensitiveIdentifiersSynthesize) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] data, Data, result;\n"
      "  assign result = data + Data;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IdentifierSynthesis, SingleCharIdentifierSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] x, y;\n"
      "  assign x = y;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IdentifierSynthesis, MaxLengthIdentifierSynthesizes) {
  SynthFixture f;
  std::string long_id(1024, 'a');
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] " +
          long_id +
          ", result;\n"
          "  assign result = " +
          long_id +
          ";\n"
          "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IdentifierSynthesis, MixedCharClassIdentifiersSynthesize) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic [7:0] _start, mid$dle, end_99, result;\n"
      "  assign result = _start + mid$dle + end_99;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

// §5.6: "If an identifier exceeds the implementation-specific length limit,
// an error shall be reported." A 1025-character identifier reaching the
// synthesizer-stage pipeline must cause an error on the diagnostic engine.
TEST(IdentifierSynthesis, IdentifierExceedingMaxLengthReportsError) {
  SynthFixture f;
  std::string long_id(1025, 'a');
  ElaborateSrc(f, "module m;\n"
                  "  logic " +
                      long_id +
                      ";\n"
                      "endmodule\n");
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
