// Tests for the head text of IEEE 1800-2023 §9.3 "Block statements" (the prose
// printed before §9.3.1). Two runtime requirements live in the head: the
// statements of a sequential block execute sequentially in the given order, and
// the statements of a parallel block execute concurrently. Both are observed
// end to end (parse, elaborate, run) so the behavior reflects real block source
// rather than a hand-built process state. Join-type semantics, start/finish
// timing, and naming belong to the descendant subclauses §9.3.1-§9.3.5.
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §9.3 head: statements in a sequential block execute in the given order. The
// second statement reads what the first wrote, so the observed value is proof
// of in-order execution -- a reordered run would read the still-default source.
// The block also sits in a single-statement position (an if then-branch),
// tying the ordering guarantee to the head's "acts as a single statement" role.
TEST(BlockStatementSimulation, SequentialBlockExecutesInGivenOrder) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] a, b;\n"
                      "  initial\n"
                      "    if (1'b1)\n"
                      "      begin\n"
                      "        a = 8'd5;\n"
                      "        b = a + 8'd1;\n"
                      "      end\n"
                      "endmodule\n",
                      "b"),
            6u);
}

// §9.3 head: statements in a parallel block execute concurrently. One member
// waits on a named event while a sibling member triggers it after a delay. Only
// concurrent execution lets the waiter observe the trigger; sequential
// execution of the members would block the first forever and leave the target
// at its default. Observing the written value therefore discriminates
// concurrent from sequential execution.
TEST(BlockStatementSimulation, ParallelBlockMembersExecuteConcurrently) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  event ev;\n"
                      "  logic [7:0] a;\n"
                      "  initial fork\n"
                      "    begin @(ev); a = 8'd1; end\n"
                      "    begin #5 ->ev; end\n"
                      "  join\n"
                      "endmodule\n",
                      "a"),
            1u);
}

}  // namespace
