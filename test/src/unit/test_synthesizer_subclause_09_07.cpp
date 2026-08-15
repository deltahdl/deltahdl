#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// §9.7 declares `process` a built-in class and `process::self()` a static
// function returning a handle to the calling process, and the synthesizer has
// no report of its own for either. The module below is rejected all the same,
// under §9.2.1, because SynthLower::CheckSynthesizable passes over the body of
// an initial procedure and reports the procedure itself when the module
// describes no other hardware. The declaration on line 3 is never examined,
// which is why the case names the report it gets rather than claiming coverage
// of §9.7 this source cannot give.
TEST(FineGrainProcessControlSynthesis,
     ProcessDeclInsideInitialDrawsTheProcedureReport) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  initial begin\n"
                           "    process p = process::self();\n"
                           "  end\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "initial procedure is not synthesizable", 2,
                            "9.2.1"));
}

}  // namespace
