#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(NameSpaceSynthesis, ModuleNameSpaceLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module child;\n"
                           "  logic sig;\n"
                           "endmodule\n"
                           "module top;\n"
                           "  parameter int P = 4;\n"
                           "  logic [P-1:0] data;\n"
                           "  child c();\n"
                           "  assign data = '0;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(NameSpaceSynthesis, PortReintroducedAsNetLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module top(data);\n"
                           "  input data;\n"
                           "  wire data;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// The report comes from the elaborator, at the second declaration, before any
// graph is built. Naming it is what says the source was stopped by §3.13's
// compilation-unit name space rule rather than by anything the synthesizer
// went on to find in a module that reached it in a bad state.
TEST(NameSpaceSynthesis, DuplicateCuScopeTypedefRejectedBeforeSynth) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "typedef int t;\n"
                           "typedef int t;\n"
                           "module top;\n"
                           "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "redeclaration of 't' in compilation-unit scope", 2,
                            "3.13"));
  if (mod) {
    SynthLower synth(f.arena, f.diag);
    (void)synth.Lower(mod);
  }
}

}  // namespace
