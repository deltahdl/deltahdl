#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(ContAssignStatementSynth, AssignDirectWire) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, output y);\n"
                           "  assign y = a;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 1);
  EXPECT_EQ(aig->outputs.size(), 1);
  EXPECT_EQ(aig->outputs[0], AigLit(aig->inputs[0], false));
}

TEST(ContAssignStatementSynth, AssignConstant) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(output y);\n"
                           "  assign y = 1'b1;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstTrue);
}

TEST(ContAssignStatementSynth, AssignConstantZero) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(output y);\n"
                           "  assign y = 1'b0;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstFalse);
}

TEST(ContAssignStatementSynth, PassthroughWire) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module m(input a, output y);\n"
      "  assign y = a;\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 1);
  EXPECT_EQ(aig->outputs.size(), 1);
}

TEST(ContAssignStatementSynth, ConstantZeroOutputCount) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module m(output y);\n"
      "  assign y = 1'b0;\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs.size(), 1);
}

}  // namespace
