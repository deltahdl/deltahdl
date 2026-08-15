#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// The whole module written on one line still puts the report on that line,
// which is the line the `final` keyword stands on.
TEST(FinalProcedureSynthesis, RejectFinalBlock) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f, "module m; final begin end endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "final procedure is not synthesizable", 1,
                            "9.2.3"));
}

// §9.2.3: a final procedure occurs at the end of simulation time, so a module
// whose only content is one has no hardware to synthesize. It is a different
// construct from the initial procedure of §9.2.1 and reads differently, which
// one shared sentence about "initial/final" could not do.
TEST(FinalProcedureSynthesis, FinalProcedureIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  final begin\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  const Diagnostic* d = FindDiag(f, "final procedure is not synthesizable");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->subclause, "9.2.3");
  EXPECT_EQ(d->loc.line, 2u);
}

}  // namespace
