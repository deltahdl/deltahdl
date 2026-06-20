#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
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

TEST(HierarchicalNameSynthesis, HierarchicalNameReadInAssignmentLowers) {
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
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

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
  EXPECT_TRUE(f.diag.HasErrors());
  if (mod) {
    SynthLower synth(f.arena, f.diag);
    (void)synth.Lower(mod);
  }
}

}  // namespace
