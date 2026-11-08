#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(BuiltinMethodSynth, ArraySizeCallIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] arr [0:3];\n"
                           "  logic [31:0] s;\n"
                           "  assign s = arr.size();\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a function call has no lowering in the "
                            "synthesizer",
                            4, "13.4"));
}

TEST(BuiltinMethodSynth, ArraySizeWithoutParenthesesIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] arr [0:2];\n"
                           "  logic [31:0] s;\n"
                           "  assign s = arr.size;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a member of a packed structure has no lowering in "
                            "the synthesizer",
                            4, "7.2.1"));
}

}  // namespace
