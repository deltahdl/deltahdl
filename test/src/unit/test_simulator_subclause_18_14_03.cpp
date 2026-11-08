#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

const char* const kClasses =
    "  class C1;\n"
    "    rand integer x;\n"
    "  endclass\n"
    "  class C2;\n"
    "    rand integer y;\n"
    "  endclass\n";

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
