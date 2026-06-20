#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §16.7's concatenation rule states that ##N specifies a delay of N clock
// ticks; the SVA engine helper that checks the cycle-by-cycle Boolean
// sequence underlies the named-sequence machinery exercised here.

TEST(CycleDelayConcat, ParenthesizedRepetitionSequenceRegisters) {
  // §16.7 sequence_abbrev on a parenthesized sequence_expr survives
  // through to lowering; the lowerer still registers the named sequence.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b;\n"
      "  sequence rep;\n"
      "    @(posedge clk) (a ##1 b)[*2];\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_NE(f.ctx.FindSequenceDecl("rep"), nullptr);
}

TEST(CycleDelayConcat, NamedSequenceWithConcatRegisters) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b, c;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b ##2 c;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_NE(f.ctx.FindSequenceDecl("abc"), nullptr);
  auto* ep = f.ctx.FindVariable("__seq_abc");
  ASSERT_NE(ep, nullptr);
  EXPECT_TRUE(ep->is_event);
}

}  // namespace
