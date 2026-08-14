#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// A positional assignment pattern reaches SynthLower::LowerExprBit as
// ExprKind::kAssignmentPattern, and the synthesizer has no lowering for it, so
// it reports the pattern under §10.9 and SynthLower::Lower answers with
// nothing. The case used to assert only that a graph came back, which held
// while kAssignmentPattern fell through to constant zero: every bit of `x` came
// out zero rather than 16'h1234, and nothing said so.
TEST(AssignmentPatternSynth, PositionalPatternIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [15:0] x;\n"
                           "  assign x = '{8'h12, 8'h34};\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment pattern has no lowering in the "
                            "synthesizer",
                            3, "10.9"));
}

// Parser::ParseTypeRefPrimary builds `type(x)'{...}` as a cast over the
// pattern, so the kind SynthLower::LowerExprBit meets is ExprKind::kCast and
// the report names §6.24.1 rather than §10.9. The case used to assert only that
// a graph came back, which held while kCast fell through to constant zero.
TEST(AssignmentPatternSynth, TypePrefixedPatternIsReportedUnloweredAsACast) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [15:0] x;\n"
                           "  assign x = type(x)'{8'd1, 8'd2};\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a cast has no lowering in the synthesizer", 3,
                            "6.24.1"));
}

// The replication form of an assignment pattern is the same
// ExprKind::kAssignmentPattern node and draws the same §10.9 report. The case
// used to assert only that a graph came back, which held while the pattern
// contributed constant zero to all thirty-two bits of `x` instead of four
// copies of 8'hAB.
TEST(AssignmentPatternSynth, ReplicationPatternIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [31:0] x;\n"
                           "  assign x = '{4{8'hAB}};\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment pattern has no lowering in the "
                            "synthesizer",
                            3, "10.9"));
}

}  // namespace
