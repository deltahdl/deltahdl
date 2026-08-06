#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §6.20.6: unlike a localparam (fixed during elaboration), a const may be set
// during simulation. An automatic const local to a subroutine takes its value
// from a run-time argument each time the subroutine is entered. A single call
// observes the const being computed at run time from the passed argument.
TEST(ConstConstantSim, AutomaticConstTakesRuntimeArgumentValue) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int result;\n"
                      "  function automatic int add_one(int a);\n"
                      "    const int c = a + 1;\n"
                      "    return c;\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    result = add_one(41);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

// §6.20.6: the automatic const is re-evaluated on every invocation, so two
// calls with different arguments yield different const values within the same
// simulation. A value fixed at elaboration could not vary between calls; this
// distinguishes a const from a localparam.
TEST(ConstConstantSim, AutomaticConstReevaluatedEachCall) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r1, r2;\n"
      "  function automatic int add_one(int a);\n"
      "    const int c = a + 1;\n"
      "    return c;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    r1 = add_one(10);\n"
      "    r2 = add_one(20);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 11u}, {"r2", 21u}});
}

}  // namespace
