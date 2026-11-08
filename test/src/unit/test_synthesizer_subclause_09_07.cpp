#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(FineGrainProcessControlSynthesis,
     ProcessDeclInsideInitialDrawsTheProcedureReport) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  initial begin\n"
                           "    static process p = process::self();\n"
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

TEST(FineGrainProcessControlSynthesis,
     ProcessDeclInsideAlwaysCombDrawsTheProcessHandleReport) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  always_comb begin\n"
                           "    static process p = process::self();\n"
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

TEST(FineGrainProcessControlSynthesis,
     ProcessDeclInsideAlwaysCombYieldsNoNetlist) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  always_comb begin\n"
                           "    static process p = process::self();\n"
                           "  end\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a process control handle has no lowering in the synthesizer", 3, "9.7"));
}

}  // namespace
