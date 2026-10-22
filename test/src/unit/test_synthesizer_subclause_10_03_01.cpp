#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// The headers are non-ANSI, since §23.2.2.1 bars declaring an ANSI port again;
// a non-ANSI port declared without a net type may be declared again as a net,
// here with a net declaration assignment.
TEST(NetDeclAssignSynth, NetDeclAssignConstant) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(y);\n"
                           "  output y;\n"
                           "  wire y = 1'b1;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs.size(), 1);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstTrue);
}

TEST(NetDeclAssignSynth, NetDeclAssignPassthrough) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(a, y);\n"
                           "  input a;\n"
                           "  output y;\n"
                           "  wire y = a;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 1);
  EXPECT_EQ(aig->outputs.size(), 1);
  EXPECT_EQ(aig->outputs[0], AigLit(aig->inputs[0], false));
}

}  // namespace
