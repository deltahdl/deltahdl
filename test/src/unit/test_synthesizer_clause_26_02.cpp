#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(PackageDeclarationSynthesis, EmptyPackageDoesNotBlockSynthesis) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "package pkg;\n"
                           "endpackage\n"
                           "module top;\n"
                           "  logic sig;\n"
                           "  assign sig = 1'b0;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackageDeclarationSynthesis, PackageWithParameterCoexistsWithModule) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "package pkg;\n"
                           "  parameter int W = 4;\n"
                           "endpackage\n"
                           "module top;\n"
                           "  logic [3:0] bus;\n"
                           "  assign bus = '0;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
