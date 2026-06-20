#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
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

TEST(NameSpaceSynthesis, DuplicateCuScopeTypedefRejectedBeforeSynth) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "typedef int t;\n"
                           "typedef int t;\n"
                           "module top;\n"
                           "endmodule\n");
  EXPECT_TRUE(f.diag.HasErrors());
  if (mod) {
    SynthLower synth(f.arena, f.diag);
    (void)synth.Lower(mod);
  }
}

}  // namespace
