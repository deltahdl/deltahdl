#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §18.13.4: get_randstate() returns the object's RNG internal state as a
// `string` (the `function string get_randstate()` prototype). The reported
// state is of implementation-dependent, but non-empty, length. Driven end to
// end: a real `o.get_randstate()` call feeds a string variable whose length is
// then observed.
TEST(GetRandstateSimulation, ObjectStateReturnsNonEmptyString) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    s = o.get_randstate();\n"
      "    n = (s.len() > 0) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "n"), 1u);
}

// §18.13.4: the returned string reflects the object's *current internal RNG
// state*. Two objects seeded alike (via §18.15 this.srandom in new) sit in one
// state, so their get_randstate() strings are equal; once one object's stream
// advances -- randomize() draws from and advances the object RNG -- its
// reported state diverges from the captured one. `eq` and `ne` are observed
// from real string comparison of get_randstate() results.
TEST(GetRandstateSimulation, ObjectStateReflectsCurrentRngState) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "  function new(int seed);\n"
      "    this.srandom(seed);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  string s1;\n"
      "  string s2;\n"
      "  string s3;\n"
      "  int eq;\n"
      "  int ne;\n"
      "  initial begin\n"
      "    C o1 = new(7);\n"
      "    C o2 = new(7);\n"
      "    s1 = o1.get_randstate();\n"
      "    s2 = o2.get_randstate();\n"
      "    eq = (s1 == s2) ? 1 : 0;\n"
      "    ok = o1.randomize();\n"
      "    s3 = o1.get_randstate();\n"
      "    ne = (s1 != s3) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "eq"), 1u);
  EXPECT_EQ(RunAndGet(src, "ne"), 1u);
}

// §18.13.4: get_randstate() *retrieves* -- it is a pure read that must not
// perturb the stream. Two identically seeded objects: one has its state read
// twice before randomizing, the other is not read at all. Both still produce
// the same draw, proving the reads left the generator untouched.
TEST(GetRandstateSimulation, RetrievingObjectStateDoesNotAdvanceStream) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "  function new(int seed);\n"
      "    this.srandom(seed);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  string junk;\n"
      "  int x1;\n"
      "  int x2;\n"
      "  int same;\n"
      "  initial begin\n"
      "    C o1 = new(5);\n"
      "    C o2 = new(5);\n"
      "    junk = o1.get_randstate();\n"
      "    junk = o1.get_randstate();\n"
      "    ok = o1.randomize();\n"
      "    x1 = o1.a;\n"
      "    ok = o2.randomize();\n"
      "    x2 = o2.a;\n"
      "    same = (x1 == x2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

// §18.13.4 via §9.7: the RNG associated with a process is retrieved through the
// process's get_randstate() method. Two consecutive reads with no draw between
// return an equal string (pure read); after $urandom draws from the process
// stream, a fresh get_randstate() differs -- the state tracks the generator's
// current position.
TEST(GetRandstateSimulation, ProcessStateReflectsCurrentRngState) {
  const char* src =
      "module t;\n"
      "  string s1;\n"
      "  string s2;\n"
      "  string s3;\n"
      "  int eq;\n"
      "  int ne;\n"
      "  int a;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
      "    s1 = p.get_randstate();\n"
      "    s2 = p.get_randstate();\n"
      "    eq = (s1 == s2) ? 1 : 0;\n"
      "    a = $urandom;\n"
      "    s3 = p.get_randstate();\n"
      "    ne = (s1 != s3) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "eq"), 1u);
  EXPECT_EQ(RunAndGet(src, "ne"), 1u);
}

// §18.13.4 built on §18.14 random stability: get_randstate() retrieves the
// state of *this* object's RNG only. Because each object owns an independent
// stream, draws taken from one object leave another object's reported state
// untouched. Two differently seeded objects are constructed; one is randomized
// repeatedly while the other's get_randstate() is captured before and after --
// the second object's state is unchanged by the first's activity.
TEST(GetRandstateSimulation, ObjectStateIsIndependentOfOtherObjectDraws) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "  function new(int seed);\n"
      "    this.srandom(seed);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  string before;\n"
      "  string after;\n"
      "  int unchanged;\n"
      "  initial begin\n"
      "    C o1 = new(1);\n"
      "    C o2 = new(2);\n"
      "    before = o2.get_randstate();\n"
      "    ok = o1.randomize();\n"
      "    ok = o1.randomize();\n"
      "    after = o2.get_randstate();\n"
      "    unchanged = (before == after) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "unchanged"), 1u);
}

}  // namespace
