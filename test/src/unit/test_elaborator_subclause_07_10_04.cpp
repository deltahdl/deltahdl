#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §7.10.4 lists nine ways a queue variable is updated by assignment. Each is
// legal, so the elaborator has to pass every one of them through to the
// simulator. A rule written for packed part-selects or for whole-array
// assignment compatibility that also caught a queue slice would stop the form
// before it ran, and these tests are what says it does not.

// §7.10.4: `q = { q, 6 }` elaborates.
TEST(QueueAssignElaboration, ConcatAppendOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q = {q, 6};\n"
             "endmodule\n"));
}

// §7.10.4: `q = { e, q }` elaborates.
TEST(QueueAssignElaboration, ConcatPrependOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  int e;\n"
             "  initial q = {e, q};\n"
             "endmodule\n"));
}

// §7.10.4: `q = q[1:$]` elaborates. The right-hand side is an unpacked value
// assigned to the queue whole, written with no braces around it.
TEST(QueueAssignElaboration, BareSliceOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q = q[1:$];\n"
             "endmodule\n"));
}

// §7.10.4: `q = q[0:$-1]` elaborates, with an expression over `$` as the upper
// bound.
TEST(QueueAssignElaboration, BareSliceToDollarMinusOneOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q = q[0:$-1];\n"
             "endmodule\n"));
}

// §7.10.4: `q = { q[0:pos-1], e, q[pos:$] }` elaborates. §7.10.1 rules that
// slice bounds "are not required to be constant expressions", so a bound that
// names a variable has to survive elaboration.
TEST(QueueAssignElaboration, ConcatWithVariableBoundSlicesOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  int e, pos;\n"
             "  initial q = {q[0:pos-1], e, q[pos:$]};\n"
             "endmodule\n"));
}

// §7.10.4: `q = q[2:$]`, "a new queue lacking the first two items",
// elaborates.
TEST(QueueAssignElaboration, BareSliceDroppingFirstTwoOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q = q[2:$];\n"
             "endmodule\n"));
}

// §7.10.4: `q = q[1:$-1]`, "a new queue lacking the first and last items",
// elaborates.
TEST(QueueAssignElaboration, BareSliceDroppingFirstAndLastOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q = q[1:$-1];\n"
             "endmodule\n"));
}

// §10.4.2 makes a nonblocking assignment to an element of a dynamically sized
// array illegal. The queue variable itself is not such an element, so
// `q <= { q, 6 }` elaborates.
TEST(QueueAssignElaboration, NonblockingConcatAppendOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q <= {q, 6};\n"
             "endmodule\n"));
}

// §10.4.2: `q <= q[1:$]` writes the queue variable and not an element of it,
// so it elaborates for the same reason.
TEST(QueueAssignElaboration, NonblockingBareSliceOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q <= q[1:$];\n"
             "endmodule\n"));
}

}  // namespace
