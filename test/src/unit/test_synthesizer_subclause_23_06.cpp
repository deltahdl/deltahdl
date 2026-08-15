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

// The assertion names §23.6 because `c1.sig` is a hierarchical name rather
// than a member of a packed structure. §23.6 defines the reference this source
// writes: "Any named SystemVerilog object or hierarchical name reference can be
// referenced uniquely in its full form by concatenating the names of the
// modules, module instance names, generate blocks, tasks, functions, assertion
// labels, named assertion action blocks, or named blocks that contain it. The
// period character shall be used to separate each of the names in the
// hierarchy". §23.7 is what tells the construct from a member select: "The
// distinguishing aspect of a hierarchical name is that the first component of
// the name matches a scope name while the first name component of a member
// select matches a data object or interface port name". `c1` is the instance
// name of the `child c1()` instantiation and so matches a scope name, while
// `p` in a member select `p.hi` matches a declared variable.
// Parser::ParseMemberAccessChain builds both constructs as
// ExprKind::kMemberAccess, so SynthLower is what has to tell them apart before
// it reports one. This case fails if SynthLower reports the §7.2.1
// packed-structure message for a name whose first component is a child
// instance. The case used to assert only that a graph came back and that no
// error stood, which held while kMemberAccess fell through to constant zero:
// `out` came out zero rather than 8'h2a, and nothing said so.
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a hierarchical name has no lowering in the synthesizer", 8, "23.6"));
}

// The report comes from Elaborator::ValidateHierRefIntoChecker, at the
// continuous assignment, before any graph is built. Naming its message is what
// says the source was stopped by §23.6's rule that a hierarchical reference
// into a checker shall not be permitted rather than by the report the case
// above draws. Both reports carry §23.6, because a hierarchical name that
// reaches SynthLower is reported under the subclause that defines it, so the
// message is the only thing that tells the two apart.
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
