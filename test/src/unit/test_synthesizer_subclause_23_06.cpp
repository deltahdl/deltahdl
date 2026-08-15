#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(HierarchicalNameSynthesis, ModuleInstanceHierarchyLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module child;\n"
                           "  logic [7:0] sig;\n"
                           "  assign sig = 8'h00;\n"
                           "endmodule\n"
                           "module top;\n"
                           "  child c1();\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// Parser::ParseMemberAccessChain builds the hierarchical reference `c1.sig` as
// ExprKind::kMemberAccess, the same node a member select on a packed structure
// produces, and nothing between the parser and SynthLower rewrites it. The
// synthesizer has no lowering for that kind, so it reports the reference under
// §7.2.1 and SynthLower::Lower answers with nothing. The case used to assert
// only that a graph came back and that no error stood, which held while
// kMemberAccess fell through to constant zero: `out` came out zero rather than
// 8'h2a, and nothing said so.
TEST(HierarchicalNameSynthesis, HierarchicalNameReadInAssignmentIsReported) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module child;\n"
                           "  logic [7:0] sig;\n"
                           "  assign sig = 8'h2a;\n"
                           "endmodule\n"
                           "module top;\n"
                           "  child c1();\n"
                           "  logic [7:0] out;\n"
                           "  assign out = c1.sig;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a member of a packed structure has no lowering in "
                            "the synthesizer",
                            8, "7.2.1"));
}

// The report comes from Elaborator::ValidateHierRefIntoChecker, at the
// continuous assignment, before any graph is built. Naming it is what says the
// source was stopped by §23.6's rule on hierarchical names rather than by the
// §7.2.1 report the case above draws, which a member access into a module
// instance draws too.
TEST(HierarchicalNameSynthesis, HierarchicalRefIntoCheckerRejectedBeforeSynth) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "checker my_chk;\n"
                           "  logic captured;\n"
                           "endchecker\n"
                           "module top;\n"
                           "  my_chk chk_inst();\n"
                           "  logic x;\n"
                           "  assign x = chk_inst.captured;\n"
                           "endmodule\n");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference into a checker is not permitted", 7, "23.6"));
  if (mod) {
    SynthLower synth(f.arena, f.diag);
    (void)synth.Lower(mod);
  }
}

}  // namespace
