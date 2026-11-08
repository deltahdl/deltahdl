#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

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
