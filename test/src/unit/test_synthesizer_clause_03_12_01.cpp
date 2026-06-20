#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(CompilationUnitSynthesis, CuScopeTypedefVisibleToModule) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "typedef logic [7:0] byte_t;\n"
                           "module top;\n"
                           "  byte_t data;\n"
                           "  assign data = '0;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CompilationUnitSynthesis, CuScopeLocalparamCoexistsWithModule) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "localparam int WIDTH = 4;\n"
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
