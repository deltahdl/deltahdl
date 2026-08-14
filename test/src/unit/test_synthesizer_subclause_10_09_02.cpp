#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// A structure assignment pattern reaches SynthLower::LowerExprBit as
// ExprKind::kAssignmentPattern, and the synthesizer has no lowering for it, so
// it reports the pattern under §10.9 and SynthLower::Lower answers with
// nothing. The case used to assert only that a graph came back, which held
// while kAssignmentPattern fell through to constant zero: both members of `p`
// came out zero rather than 8'h01 and 8'h02, and nothing said so.
TEST(StructPatternSynth, ConstPositionalPatternIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  assign p = '{8'h01, 8'h02};\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment pattern has no lowering in the "
                            "synthesizer",
                            4, "10.9"));
}

// Parser::TryParseUserTypeCast builds `pair_t'{...}` as a cast over the
// pattern, so the kind SynthLower::LowerExprBit meets is ExprKind::kCast and
// the report names §6.24.1 rather than §10.9. The case used to assert only that
// a graph came back, which held while kCast fell through to constant zero.
TEST(StructPatternSynth, ConstNamedPatternIsReportedUnloweredAsACast) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  assign p = pair_t'{a: 8'h01, b: 8'h02};\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a cast has no lowering in the synthesizer", 4,
                            "6.24.1"));
}

// The `default:` form of a structure pattern is the same
// ExprKind::kAssignmentPattern node and draws the same §10.9 report. The case
// used to assert only that a graph came back, which held while the pattern
// contributed constant zero to `p` -- the value 8'h00 the pattern names, which
// is why an unlowered pattern was indistinguishable from a lowered one here.
TEST(StructPatternSynth, DefaultPatternIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  assign p = '{default: 8'h00};\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment pattern has no lowering in the "
                            "synthesizer",
                            4, "10.9"));
}

}  // namespace
