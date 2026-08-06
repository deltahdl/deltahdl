#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §18.13.5: set_randstate() installs the given value as an object's RNG
// internal state. A state captured with get_randstate() and reinstalled
// afterwards restores the generator to the exact stream position it was read
// from, so the randomize() draws taken after the restore replay the draws that
// followed the capture. Driven end-to-end: the state string is produced by real
// get_randstate() source, round-tripped through a string variable, and consumed
// by set_randstate(). `differ` proves the stream advances between draws, so
// `same` is not a trivial coincidence.
TEST(SetRandstateSimulation, RestoresCapturedObjectStream) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  string s;\n"
      "  int a1;\n"
      "  int a2;\n"
      "  int b1;\n"
      "  int b2;\n"
      "  int same;\n"
      "  int differ;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    s = o.get_randstate();\n"
      "    ok = o.randomize();\n"
      "    a1 = o.a;\n"
      "    ok = o.randomize();\n"
      "    a2 = o.a;\n"
      "    o.set_randstate(s);\n"
      "    ok = o.randomize();\n"
      "    b1 = o.a;\n"
      "    ok = o.randomize();\n"
      "    b2 = o.a;\n"
      "    same = (a1 == b1 && a2 == b2) ? 1 : 0;\n"
      "    differ = (a1 != a2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
  EXPECT_EQ(RunAndGet(src, "differ"), 1u);
}

// §18.13.5: the state value captures generator state, not object identity, so
// it is portable between objects. A state read from one object and installed
// into a second (never itself drawn from) makes the second continue the first's
// stream: their next draws agree. This also exercises installing a state into
// an object whose stream has not yet been materialized.
TEST(SetRandstateSimulation, TransfersStateBetweenObjects) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  string s;\n"
      "  int same;\n"
      "  initial begin\n"
      "    C o1 = new;\n"
      "    C o2 = new;\n"
      "    // Advance o1, then capture and hand its state to o2.\n"
      "    ok = o1.randomize();\n"
      "    s = o1.get_randstate();\n"
      "    o2.set_randstate(s);\n"
      "    ok = o1.randomize();\n"
      "    ok = o2.randomize();\n"
      "    same = (o1.a == o2.a) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

// §18.13.5 via §9.7: the RNG associated with a process is set using the
// set_randstate() method of the process. Capturing the current process's state,
// drawing $urandom values (which draw from that process's stream), then
// reinstalling the state rewinds the generator so the same values are drawn
// again. `differ` confirms the stream advances so `same` is meaningful.
TEST(SetRandstateSimulation, RestoresCapturedProcessStream) {
  const char* src =
      "module t;\n"
      "  string s;\n"
      "  int a1;\n"
      "  int a2;\n"
      "  int b1;\n"
      "  int b2;\n"
      "  int same;\n"
      "  int differ;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
      "    s = p.get_randstate();\n"
      "    a1 = $urandom;\n"
      "    a2 = $urandom;\n"
      "    p.set_randstate(s);\n"
      "    b1 = $urandom;\n"
      "    b2 = $urandom;\n"
      "    same = (a1 == b1 && a2 == b2) ? 1 : 0;\n"
      "    differ = (a1 != a2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
  EXPECT_EQ(RunAndGet(src, "differ"), 1u);
}

}  // namespace
