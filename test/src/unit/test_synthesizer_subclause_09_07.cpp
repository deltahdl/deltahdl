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

// §9.7 makes `process` a built-in class and process::self() a static method
// returning a handle to the calling process, and no hardware holds one. The
// declaration below stands inside an always_comb procedure, which
// SynthLower::CheckSynthesizable walks rather than passes over, so
// SynthLower::CheckDeclSynthesizable reaches the declared type and reports it
// under §9.7 in its own right rather than under the §9.2.1 rule the initial
// procedure above is rejected by.
TEST(FineGrainProcessControlSynthesis,
     ProcessDeclInsideAlwaysCombDrawsTheProcessHandleReport) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  always_comb begin\n"
                           "    process p = process::self();\n"
                           "  end\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  synth.Lower(mod);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a process control handle has no lowering in the "
                            "synthesizer",
                            3, "9.7"));
}

// The same source gets no graph back. A report and a netlist together would
// hand a design that declares a §9.7 process handle a netlist describing
// something other than what was written, since the declaration lowers to
// nothing, so the rejection is what the design has to be given.
TEST(FineGrainProcessControlSynthesis,
     ProcessDeclInsideAlwaysCombYieldsNoNetlist) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  always_comb begin\n"
                           "    process p = process::self();\n"
                           "  end\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
}

}  // namespace
