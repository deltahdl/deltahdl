// The `c` half of the §9.4.2 event-control family. Where the `a` and `b` files
// vary the writer, this file varies the operand: an element of a fixed-size
// unpacked array, which is a Variable of its own that a write notifies under
// its own name and never under the array's, and an element of an array port,
// which the parent's port binding writes from outside the instance whose
// process waits on it.

#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §9.4.2: an element of a fixed-size unpacked array is a lawful operand, so
// `@(posedge c[0])` wakes on each rising edge of that element alone, four in
// 41 time units, while c[1] toggling as well wakes it no more often; `@(c[j])`
// with j naming the other element wakes on each of c[1]'s nine changes, the
// first from x to 0. The watcher was armed on the array's name, which no
// element write notifies, so both counts stayed 0.
TEST(EventControlSim, AnUnpackedArrayElementWakesItsEventControl) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  logic c[2];\n"
                       "  int k = 0, w = 0, j = 1;\n"
                       "  always @(posedge c[0]) k++;\n"
                       "  always @(c[j]) w++;\n"
                       "  initial begin\n"
                       "    c[0] = 0; c[1] = 0;\n"
                       "    forever #5 begin c[0] = ~c[0]; c[1] = ~c[1]; end\n"
                       "  end\n"
                       "  initial #41 $display(\"%0d %0d\", k, w);\n"
                       "  initial #45 $finish;\n"
                       "endmodule\n",
                       f),
            "4 9\n$finish at time 45\n");
}

// §9.4.2 with §23.9: `@(posedge c[0])` in an instance whose array input port c
// the parent drives names the instance's c, though the parent's port binding
// is the process writing it. The watcher re-evaluated the operand under that
// writer, where `c[0]` names nothing, saw no change, and never woke.
TEST(EventControlSim, AnArrayPortElementWakesTheInstancesEventControl) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module p(input logic c[2]);\n"
                       "  int k = 0;\n"
                       "  always @(posedge c[0]) k++;\n"
                       "  initial #41 $display(\"k=%0d\", k);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  logic cs[2] = '{0, 0};\n"
                       "  always #5 cs[0] = ~cs[0];\n"
                       "  p u(cs);\n"
                       "  initial #45 $finish;\n"
                       "endmodule\n",
                       f),
            "k=4\n$finish at time 45\n");
}

}  // namespace
