#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// §12.7.1: the for loop is a statement whose body runs a number of times the
// loop control decides. SynthLower has no lowering for it and no rule naming
// it, so it is the case that reaches the last arm of LowerStmt, and the last
// arm is what this test is for. Before that arm existed, the loop and the
// assignment inside it left no trace in the graph while `Lower` answered with
// a netlist and the run reported success.
//
// The report carries no subclause because the design breaks no rule of IEEE
// 1800-2023 by writing a for loop: what it meets is a limit of this
// synthesizer, and the location is what tells the reader which statement is
// missing from the netlist.
TEST(SequentialLoopSynthesis, UnlowerableStatementIsReportedRatherThanDropped) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, output logic y);\n"
                           "  integer i;\n"
                           "  always_comb begin\n"
                           "    for (i = 0; i < 2; i = i + 1)\n"
                           "      y = a;\n"
                           "  end\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  const Diagnostic* d = FindDiag(f,
                                 "statement has no lowering in the synthesizer "
                                 "and would be dropped from the netlist");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->subclause, "");
  EXPECT_EQ(d->loc.line, 4u);
}

}  // namespace
