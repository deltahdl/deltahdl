#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
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

// A.6.2 admits an inc_or_dec_expression as a statement, and §11.4.2 rules that
// it behaves as a blocking assignment, so `tmp++` has to leave `tmp` carrying
// one more than it did. The sweep over every value of `a` is what states that:
// a synthesizer that passes the increment over silently still returns a graph,
// so `ASSERT_NE(aig, nullptr)` holds over a netlist in which the increment
// never happened. Every input value is driven because a single one proves
// nothing about an adder, and because at width 1 an increment and a decrement
// build the same netlist. The block writes `y` itself rather than through a
// continuous assignment, since `SynthLower::Lower` lowers a module's continuous
// assignments before its processes and a read through `assign y = tmp;` would
// measure that order instead of the increment.
TEST(ProceduralBlockSynthesis, IncDecExpressionCrossLinkInsideAlwaysComb) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input [3:0] a, output logic [3:0] y);\n"
                           "  logic [3:0] tmp;\n"
                           "  always_comb begin\n"
                           "    tmp = a;\n"
                           "    tmp++;\n"
                           "    y = tmp;\n"
                           "  end\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  for (uint64_t a = 0; a < 16; ++a) {
    EXPECT_EQ(EvalAigOutputs(*aig, a), (a + 1) & 0xFU) << "a = " << a;
  }
}

}  // namespace
