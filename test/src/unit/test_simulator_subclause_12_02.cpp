// Tests for §12.2 "Overview" at the simulator, covering the half of its rule
// that says what the eight constructs do: a procedural statement contained
// within any of them runs. §12.2 names six that activate on their own --
// initial, always, always_comb, always_latch, always_ff and final -- and two
// that activate when called, task and function.
//
// Each test below writes one procedural assignment into one container and
// reads the variable it wrote. The parser-stage file for this subclause covers
// the other half, that a procedural statement outside all eight is rejected.

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §12.2: `initial` activates automatically and runs the statement it contains.
TEST(ProceduralStatementContainmentSim, InitialRunsItsStatement) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial x = 42;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
}

// §12.2: `always` activates automatically and repeats, so the statement it
// contains runs each time the block does. Three delays elapse before the
// finish, so the count reaches 3.
TEST(ProceduralStatementContainmentSim, AlwaysRunsItsStatement) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial begin x = 0; #10 $finish; end\n"
      "  always #3 x = x + 1;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 3u);
}

// §12.2: `always_comb` activates automatically on a change of what its
// statement reads.
TEST(ProceduralStatementContainmentSim, AlwaysCombRunsItsStatement) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] x, y;\n"
      "  initial y = 7;\n"
      "  always_comb x = y + 1;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 8u);
}

// §12.2: `always_latch` activates automatically in the same way, and the
// statement it contains here is a selection statement rather than a bare
// assignment. Only the latch writes `x`, since §9.2.2.2 rules that a variable
// written by an always_latch shall be written by nothing else.
TEST(ProceduralStatementContainmentSim, AlwaysLatchRunsItsStatement) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic en;\n"
      "  logic [31:0] x, y;\n"
      "  initial begin en = 1; y = 5; end\n"
      "  always_latch if (en) x = y;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 5u);
}

// §12.2: `always_ff` activates on the edge its event control names, and runs
// the nonblocking assignment it contains.
TEST(ProceduralStatementContainmentSim, AlwaysFFRunsItsStatement) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] x, y;\n"
      "  initial begin clk = 0; x = 0; y = 9; #1 clk = 1; #1 $finish; end\n"
      "  always_ff @(posedge clk) x <= y;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 9u);
}

// §12.2: `final` activates once, after the simulation the other blocks ran in
// has ended, and runs the statement it contains then.
TEST(ProceduralStatementContainmentSim, FinalRunsItsStatement) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial begin x = 1; #5 $finish; end\n"
      "  final x = 99;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 99u);
}

// §12.2: a `task` activates when called, and the statement in its body runs
// then rather than on its own.
TEST(ProceduralStatementContainmentSim, TaskRunsItsStatementWhenCalled) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  task set_x;\n"
      "    x = 21;\n"
      "  endtask\n"
      "  initial begin x = 0; set_x(); end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 21u);
}

// §12.2: a `function` is the other construct that activates when called. Its
// body holds a local declaration, an assignment and a jump statement, three of
// the kinds §12.2 lists.
TEST(ProceduralStatementContainmentSim, FunctionRunsItsStatementsWhenCalled) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  function int add_one(input int v);\n"
      "    int t;\n"
      "    t = v + 1;\n"
      "    return t;\n"
      "  endfunction\n"
      "  initial x = add_one(16);\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 17u);
}

}  // namespace
