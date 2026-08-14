#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// The test fails on a run that answers a netlist for a module whose right-hand
// side is a §10.9 assignment pattern, which the synthesizer has no lowering
// for. `SynthLower::LowerExprBit` in src/synthesizer/synth_lower.cpp names
// `ExprKind::kAssignmentPattern` among the kinds it reports, so
// `SynthLower::Lower` answers no netlist and the report names §10.9.
//
// Until this change the case asserted only that a graph came back. That held
// while the pattern contributed constant zero at every bit of `p`, so what it
// was asserting over was a netlist in which the structure carried none of the
// values the pattern names.
TEST(StructDeclarationSynthesis,
     AssignmentPatternToAStructIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  assign p = '{8'hAB, 8'hCD};\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment pattern has no lowering", 4,
                            "10.9"));
}

// The test fails on the same gap through a pattern whose members are named and
// whose first member is itself a pattern. §10.9 covers both spellings, so the
// nesting reaches the same report rather than a second one, and the case above
// does not reach the nesting.
TEST(StructDeclarationSynthesis, NestedAssignmentPatternIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  typedef struct packed { logic [3:0] x; logic [3:0] y; } point_t;\n"
      "  typedef struct packed { point_t p; logic [7:0] tag; } record_t;\n"
      "  record_t r;\n"
      "  assign r = '{p: '{x: 4'h1, y: 4'h2}, tag: 8'hAA};\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment pattern has no lowering", 5,
                            "10.9"));
}

}  // namespace
