#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(SystemNameSynthesis, SystemFunctionInAssignIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [31:0] w;\n"
                           "  assign w = $clog2(16);\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a system task or system function has no lowering in the synthesizer", 3,
      "5.6.3"));
}

TEST(SystemNameSynthesis, SystemFunctionInAdditionIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] a, result;\n"
                           "  assign result = a + $clog2(32);\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a system task or system function has no lowering in the synthesizer", 3,
      "5.6.3"));
}

TEST(SystemNameSynthesis, SystemFunctionWithDataTypeArgIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [31:0] w;\n"
                           "  assign w = $bits(logic [7:0]);\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a system task or system function has no lowering in the synthesizer", 3,
      "5.6.3"));
}

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "system task or system function '$exit' is not synthesizable", 5,
      "5.6.3"));
}

}  // namespace
