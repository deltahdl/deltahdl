#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(UnionDeclarationSynthesis, PackedUnionLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  typedef union packed { logic [7:0] a; logic [7:0] b; } byte_u;\n"
      "  byte_u u;\n"
      "  assign u = 8'hA5;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(UnionDeclarationSynthesis, SoftPackedUnionLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  typedef union soft packed {\n"
                           "    logic [15:0] wide;\n"
                           "    logic [7:0] narrow;\n"
                           "  } su;\n"
                           "  su u;\n"
                           "  assign u = 16'hABCD;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
