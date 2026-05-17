#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// §23.6 R3: a module instance creates a new branch of the hierarchy.  After
// the elaborator binds that branch, synthesis must lower the parent without
// error.
TEST(HierarchicalNameSynthesis, ModuleInstanceHierarchyLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
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

// §23.6 R14: a hierarchical name read in an expression must survive
// synthesis lowering — the parent's RHS that reaches into a child's signal
// is a hierarchical reference recognized by §23.6.
TEST(HierarchicalNameSynthesis, HierarchicalNameReadInAssignmentLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
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
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §23.6 R15: hierarchical references into a checker are not permitted; the
// elaborator must reject this design so it never reaches the synthesizer.
TEST(HierarchicalNameSynthesis, HierarchicalRefIntoCheckerRejectedBeforeSynth) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "checker my_chk;\n"
      "  logic captured;\n"
      "endchecker\n"
      "module top;\n"
      "  my_chk chk_inst();\n"
      "  logic x;\n"
      "  assign x = chk_inst.captured;\n"
      "endmodule\n");
  EXPECT_TRUE(f.diag.HasErrors());
  if (mod) {
    SynthLower synth(f.arena, f.diag);
    (void)synth.Lower(mod);
  }
}

}  // namespace
