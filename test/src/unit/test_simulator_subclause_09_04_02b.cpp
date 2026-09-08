// The `b` half of the §9.4.2 event-control family. Where the `a` file reads the
// event control against writes made from an initial or always block, this file
// reads it against writes a subroutine call makes: once from inside a void
// function's body, and once through a function's `output` formal on copy-out.
// §9.4.2 says the event control resumes on a change to the expression however
// that change was produced, so the writer's syntax is what these cases vary.

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// A void function called with parentheses is the one writer that reaches the
// subroutine-body executor: SetupTaskCall declines it, so ExecFunctionBody runs
// the body and ExecFuncIdentifierAssign performs `x = v`. That path stored the
// value and notified nobody, and because a notification destructively moves the
// watcher vector, the always block parked on `@(x)` never ran again. The two
// calls below are therefore invisible before the fix and the count stops at the
// one wake the initial block's own write produced.
//
// A task body would not read this rule: ExecInlineTaskCall walks the body
// through ExecStmt to AssignToScalarLhs, which already notifies, so the same
// source written with a task passes either way.
TEST(EventControlSim, FunctionBodyWriteWakesAnEventControl) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  int woke;\n"
      "  function void poke(input logic [7:0] v);\n"
      "    x = v;\n"
      "  endfunction\n"
      "  always @(x) woke = woke + 1;\n"
      "  initial begin\n"
      "    x = 8'd1;\n"
      "    #1 poke(8'd2);\n"
      "    #1 poke(8'd3);\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "woke");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// The argument copy-out, which is a different route and not a second reading of
// the hole above: #3481 suspected it of the same silence, but
// WritebackOutputArgs hands the value to PerformBlockingAssign, which notifies.
// So this case passes on either side of the fix and stands as a guard on the
// route the issue questioned, pinning it beside the body write. The middle call
// writes the value already held, which the awaiter's own change gate drops, so
// a copy-out that notified unconditionally would read 3 here rather than 2.
TEST(EventControlSim, OutputFormalCopyOutWakesAnEventControl) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] y;\n"
      "  int seen;\n"
      "  function void fill(output logic [7:0] o, input logic [7:0] v);\n"
      "    o = v;\n"
      "  endfunction\n"
      "  always @(y) seen = seen + 1;\n"
      "  initial begin\n"
      "    fill(y, 8'd9);\n"
      "    #1 fill(y, 8'd9);\n"
      "    #1 fill(y, 8'd4);\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "seen");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

}  // namespace
