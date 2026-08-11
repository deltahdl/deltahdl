#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(SystemNameSynthesis, SystemFunctionInAssignSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [31:0] w;\n"
                           "  assign w = $clog2(16);\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(SystemNameSynthesis, SystemFunctionInExpressionSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] a, result;\n"
                           "  assign result = a + $clog2(32);\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(SystemNameSynthesis, SystemFunctionWithDataTypeArgSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [31:0] w;\n"
                           "  assign w = $bits(logic [7:0]);\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

// §5.6.3: a system construct is not design semantics but refers to simulator
// functionality, so it has no hardware to become. The report names the callee
// and stands at the `$`, so a design calling several says which one and where.
TEST(SystemNameSynthesis, SystemCallIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic x;\n"
                           "  always_comb begin\n"
                           "    x = 1'b0;\n"
                           "    $exit();\n"
                           "  end\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  const Diagnostic* d = FindDiag(
      f, "system task or system function '$exit' is not synthesizable");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->subclause, "5.6.3");
  EXPECT_EQ(d->loc.line, 5u);
}

}  // namespace
