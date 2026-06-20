#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(ProceduralBlockSynthesis, AlwaysCombBlockLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, input b, output y);\n"
                           "  always_comb y = a & b;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProceduralBlockSynthesis, AlwaysLatchBlockLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input en, input d, output q);\n"
                           "  always_latch if (en) q = d;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProceduralBlockSynthesis, AlwaysFFBlockLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input clk, input d, output q);\n"
                           "  always_ff @(posedge clk) q <= d;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProceduralBlockSynthesis, AlwaysStarBlockLowersAsComb) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, input b, output y);\n"
                           "  reg ry;\n"
                           "  always @(*) ry = a | b;\n"
                           "  assign y = ry;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProceduralBlockSynthesis, FinalBlockBypassedDuringSynthCheck) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, output y);\n"
                           "  assign y = a;\n"
                           "  final begin end\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);

  bool saw_final = false;
  for (const auto& p : mod->processes) {
    if (p.kind == RtlirProcessKind::kFinal) saw_final = true;
  }
  EXPECT_TRUE(saw_final);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);

  EXPECT_NE(aig, nullptr);
}

TEST(ProceduralBlockSynthesis, InitialBlockBypassedDuringSynthCheck) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, output y);\n"
                           "  assign y = a;\n"
                           "  initial y = 1'b0;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);

  bool saw_initial = false;
  for (const auto& p : mod->processes) {
    if (p.kind == RtlirProcessKind::kInitial) saw_initial = true;
  }
  EXPECT_TRUE(saw_initial);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);

  EXPECT_NE(aig, nullptr);
}

TEST(ProceduralBlockSynthesis, BlockingAssignmentInsideAlwaysCombLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input [3:0] a, output [3:0] y);\n"
                           "  reg [3:0] tmp;\n"
                           "  always_comb begin\n"
                           "    tmp = a;\n"
                           "  end\n"
                           "  assign y = tmp;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProceduralBlockSynthesis, NonblockingAssignmentInsideAlwaysFFLowers) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input clk, input [3:0] d, output [3:0] q);\n"
                   "  reg [3:0] qreg;\n"
                   "  always_ff @(posedge clk) qreg <= d;\n"
                   "  assign q = qreg;\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProceduralBlockSynthesis, IncDecExpressionCrossLinkInsideAlwaysComb) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input [3:0] a, output [3:0] y);\n"
                           "  reg [3:0] tmp;\n"
                           "  always_comb begin\n"
                           "    tmp = a;\n"
                           "    tmp++;\n"
                           "  end\n"
                           "  assign y = tmp;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
