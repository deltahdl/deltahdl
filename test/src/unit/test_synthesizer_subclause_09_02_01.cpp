#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(InitialProcedureSynthesis, RejectInitialBlock) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f, "module m; initial begin end endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §9.2.1: an initial procedure executes once and then ceases, so a module
// whose only content is one has no hardware to synthesize. The report names
// the initial procedure rather than lumping it in with the final procedure of
// §9.2.3, which is a different construct in a different subclause.
TEST(InitialProcedureSynthesis, InitialProcedureIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  initial begin\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  const Diagnostic* d = FindDiag(f, "initial procedure is not synthesizable");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->subclause, "9.2.1");
  EXPECT_EQ(d->loc.line, 2u);
}

// The first of two initial procedures is the one reported, so the position on
// the report belongs to a procedure the module actually holds rather than to
// whichever one the loop happened to end on.
TEST(InitialProcedureSynthesis, FirstOfTwoInitialProceduresIsReported) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  reg x;\n"
                           "  initial begin\n"
                           "    x = 0;\n"
                           "  end\n"
                           "  initial begin\n"
                           "    x = 1;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  const Diagnostic* d = FindDiag(f, "initial procedure is not synthesizable");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->loc.line, 3u);
}

}  // namespace
