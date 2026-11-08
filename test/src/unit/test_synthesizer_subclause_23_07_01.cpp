#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

namespace {

TEST(ScopeResolutionPrefixSynthesis, PackagePrefixParamSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "package pkg;\n"
                           "  parameter int WIDTH = 8;\n"
                           "endpackage\n"
                           "module t(input logic [pkg::WIDTH-1:0] a,\n"
                           "         output logic [pkg::WIDTH-1:0] y);\n"
                           "  assign y = a;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(ScopeResolutionPrefixSynthesis,
     PackageVariableReadInAssignmentIsReported) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "package pkg;\n"
                           "  logic [7:0] level;\n"
                           "endpackage\n"
                           "module t(output logic [7:0] y);\n"
                           "  assign y = pkg::level;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  (void)synth.Lower(mod);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a name with a scope resolution operator prefix "
                            "has no lowering in the synthesizer",
                            5, "23.7.1"));
}

}  // namespace
