// §3.4: A program block "provides a syntactic context that specifies
// scheduling in the reactive region set." Initials inside a program block
// therefore run in the reactive set, which executes after the active-set
// NBA region within the same simulation time step. These tests observe that
// scheduling through the resulting execution order.

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A module initial schedules an NBA on `b` (active-set NBA region) then
// terminates. A program initial reads `b` into `c`. If the program initial
// were scheduled in the active region, it would run before the NBA fires and
// observe b == 0x00. Because §3.4 places program processes in the reactive
// set, which drains after NBA, the program reads the post-NBA value 0xAA.
TEST(ProgramReactiveSim, ProgramInitialObservesNbaUpdateFromModuleInitial) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] b, c;\n"
      "  initial begin\n"
      "    b = 8'h00;\n"
      "    c = 8'h00;\n"
      "    b <= 8'hAA;\n"
      "  end\n"
      "  program p;\n"
      "    initial c = b;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0xAAu);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 0xAAu);
}

// An NBA inside a program initial must route into the reactive-set NBA
// region (ReNBA), not the active-set NBA region. We observe this by
// preceding a `#0` blocking statement: a `#0` from a reactive context
// suspends until ReInactive, which runs *before* ReNBA. So reading the NBA
// target right after the `#0` returns the pre-NBA value. If the program
// initial were running in the active set, the `#0` would suspend until
// active Inactive, after which active NBA fires and the NBA target would
// already hold the new value.
TEST(ProgramReactiveSim, ProgramInitialNbaRoutedToReactiveNbaRegion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] b, snap;\n"
      "  program p;\n"
      "    initial begin\n"
      "      b = 8'd0;\n"
      "      snap = 8'd0;\n"
      "      b <= 8'd7;\n"
      "      #0;\n"
      "      snap = b;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("snap")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 7u);
}

// Multiple initials inside a program block all run in the reactive set: each
// observes NBA-completed values from any module-side active-region writes.
TEST(ProgramReactiveSim, MultipleProgramInitialsAllRunInReactiveSet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] x, a, b;\n"
      "  initial begin x = 8'h00; x <= 8'h55; end\n"
      "  program p;\n"
      "    initial a = x;\n"
      "    initial b = x;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0x55u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0x55u);
}

}  // namespace
