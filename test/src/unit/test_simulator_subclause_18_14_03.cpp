#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// The two classes of the clause's example, each with one rand integer.
const char* const kClasses =
    "  class C1;\n"
    "    rand integer x;\n"
    "  endclass\n"
    "  class C2;\n"
    "    rand integer y;\n"
    "  endclass\n";

// 18.14.3: calls to randomize() are independent of calls to other randomize
// functions, so the clause's example run again with a $random, a $urandom and
// a std::randomize() between its two calls returns the same c1.x and c2.y,
// as the design test/src/e2e/object_stability.sv runs it.
TEST(ObjectStabilityRun, OtherRandomizeFunctionsBetweenTheCallsChangeNothing) {
  SimFixture f;
  std::string out = RunCapture(std::string("module t;\n") + kClasses +
                                   "  C1 c1;\n"
                                   "  C2 c2;\n"
                                   "  process p;\n"
                                   "  integer z, xa, ya;\n"
                                   "  int unsigned k;\n"
                                   "  int v, ok, agree = 0;\n"
                                   "  initial begin\n"
                                   "    p = process::self();\n"
                                   "    p.srandom(9);\n"
                                   "    c1 = new(); c2 = new();\n"
                                   "    void'(c1.randomize());\n"
                                   "    void'(c2.randomize());\n"
                                   "    xa = c1.x; ya = c2.y;\n"
                                   "    p.srandom(9);\n"
                                   "    c1 = new(); c2 = new();\n"
                                   "    void'(c1.randomize());\n"
                                   "    z = $random;\n"
                                   "    k = $urandom;\n"
                                   "    ok = std::randomize(v);\n"
                                   "    void'(c2.randomize());\n"
                                   "    if (c1.x == xa) agree++;\n"
                                   "    if (c2.y == ya) agree++;\n"
                                   "    $display(\"%0d\", agree);\n"
                                   "  end\n"
                                   "endmodule\n",
                               f);
  EXPECT_EQ(out, "2\n");
}

// 18.14.3: c1.x and c2.y are independent of each other and each instance has
// a unique source of random values that can be seeded independently, so c1.x
// is the same after five more calls on c2, two instances seeded with 3 draw
// the same four values, and c1 seeded with 3 again replays its four, as the
// design test/src/e2e/object_stability.sv runs it.
TEST(ObjectStabilityRun, EachInstanceIsItsOwnSourceSeededIndependently) {
  SimFixture f;
  std::string out = RunCapture(
      std::string("module t;\n") + kClasses +
          "  C1 c1, d1;\n"
          "  C2 c2;\n"
          "  process p;\n"
          "  integer xa, sa[4], sb[4], sc[4];\n"
          "  int i, others, alike = 0, replayed = 0;\n"
          "  initial begin\n"
          "    p = process::self();\n"
          "    p.srandom(9);\n"
          "    c1 = new(); c2 = new();\n"
          "    void'(c1.randomize());\n"
          "    xa = c1.x;\n"
          "    p.srandom(9);\n"
          "    c1 = new(); c2 = new();\n"
          "    for (i = 0; i < 5; i++) void'(c2.randomize());\n"
          "    void'(c1.randomize());\n"
          "    others = c1.x == xa;\n"
          "    c1.srandom(3);\n"
          "    d1 = new();\n"
          "    d1.srandom(3);\n"
          "    for (i = 0; i < 4; i++) begin void'(c1.randomize()); sa[i] = "
          "c1.x; end\n"
          "    for (i = 0; i < 4; i++) begin void'(d1.randomize()); sb[i] = "
          "d1.x; end\n"
          "    c1.srandom(3);\n"
          "    for (i = 0; i < 4; i++) begin void'(c1.randomize()); sc[i] = "
          "c1.x; end\n"
          "    for (i = 0; i < 4; i++) if (sa[i] == sb[i]) alike++;\n"
          "    for (i = 0; i < 4; i++) if (sa[i] == sc[i]) replayed++;\n"
          "    $display(\"%0d %0d %0d\", others, alike, replayed);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "1 4 4\n");
}

// 18.14.3: an instance's random seed is taken from the parent thread when
// the instance is created, so an instance seeded by hand with the value the
// thread would have drawn next draws what the one created there drew, as the
// design test/src/e2e/object_stability.sv runs it.
TEST(ObjectStabilityRun, TheSeedIsTakenFromTheParentThreadAtCreation) {
  SimFixture f;
  std::string out = RunCapture(std::string("module t;\n") + kClasses +
                                   "  C1 c1, d1;\n"
                                   "  process p;\n"
                                   "  integer xd;\n"
                                   "  int unsigned seedv;\n"
                                   "  int from_parent;\n"
                                   "  initial begin\n"
                                   "    p = process::self();\n"
                                   "    p.srandom(9);\n"
                                   "    c1 = new();\n"
                                   "    void'(c1.randomize());\n"
                                   "    xd = c1.x;\n"
                                   "    p.srandom(9);\n"
                                   "    seedv = $urandom;\n"
                                   "    d1 = new();\n"
                                   "    d1.srandom(seedv);\n"
                                   "    void'(d1.randomize());\n"
                                   "    from_parent = d1.x == xd;\n"
                                   "    $display(\"%0d\", from_parent);\n"
                                   "  end\n"
                                   "endmodule\n",
                               f);
  EXPECT_EQ(out, "1\n");
}

}  // namespace
