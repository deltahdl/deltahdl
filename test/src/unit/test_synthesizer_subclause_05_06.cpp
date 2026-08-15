#include <gtest/gtest.h>

#include <string>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(IdentifierSynthesis, SimpleIdentifierSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
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
  auto* mod = ElaborateSrc(f,
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
  auto* mod = ElaborateSrc(f,
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
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] data, Data, result;\n"
                           "  assign result = data + Data;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(IdentifierSynthesis, MaxLengthIdentifierSynthesizes) {
  SynthFixture f;
  std::string long_id(1024, 'a');
  auto* mod = ElaborateSrc(f,
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

// The report comes from the lexer, which measures the identifier as it reads
// it, so the source never reaches the synthesizer at all. Naming it is what
// says the length was what stopped this source: an identifier of 1025 letters
// is otherwise a legal declaration, and any other rejection would mean the
// case had stopped covering the limit §5.6 leaves to the implementation.
TEST(IdentifierSynthesis, IdentifierExceedingMaxLengthReportsError) {
  SynthFixture f;
  std::string long_id(1025, 'a');
  ElaborateSrc(f,
               "module m;\n"
               "  logic " +
                   long_id +
                   ";\n"
                   "endmodule\n");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "identifier exceeds maximum length of 1024 characters", 2, "5.6"));
}

}  // namespace
