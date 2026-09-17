#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// 18.13.3: srandom seeds an object's RNG with the given seed, so four
// randomize() draws of a Packet after srandom(7) are replayed in full after a
// second srandom(7) and after srandom(3 + 4), changed by srandom(8), and
// matched by a second Packet seeded with 7, as the design
// test/src/e2e/srandom_method.sv runs it.
TEST(SrandomRun, TheSeedSelectsAnObjectsSequence) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class Packet;\n"
      "    rand bit [15:0] payload;\n"
      "    rand bit [3:0] kind;\n"
      "  endclass\n"
      "  Packet a, b;\n"
      "  int i, k, replayed = 0, by_expr = 0, diverged = 0, alike = 0;\n"
      "  bit [19:0] sa[4], sb[4];\n"
      "  initial begin\n"
      "    a = new; b = new;\n"
      "    a.srandom(7);\n"
      "    for (i = 0; i < 4; i++) begin k = a.randomize(); sa[i] = {a.kind, "
      "a.payload}; end\n"
      "    a.srandom(7);\n"
      "    for (i = 0; i < 4; i++) begin k = a.randomize(); sb[i] = {a.kind, "
      "a.payload}; end\n"
      "    for (i = 0; i < 4; i++) if (sa[i] == sb[i]) replayed++;\n"
      "    a.srandom(3 + 4);\n"
      "    for (i = 0; i < 4; i++) begin k = a.randomize(); sb[i] = {a.kind, "
      "a.payload}; end\n"
      "    for (i = 0; i < 4; i++) if (sa[i] == sb[i]) by_expr++;\n"
      "    a.srandom(8);\n"
      "    for (i = 0; i < 4; i++) begin k = a.randomize(); sb[i] = {a.kind, "
      "a.payload}; end\n"
      "    for (i = 0; i < 4; i++) if (sa[i] != sb[i]) diverged = 1;\n"
      "    b.srandom(7);\n"
      "    for (i = 0; i < 4; i++) begin k = b.randomize(); sb[i] = {b.kind, "
      "b.payload}; end\n"
      "    for (i = 0; i < 4; i++) if (sa[i] == sb[i]) alike++;\n"
      "    $display(\"%0d %0d %0d %0d\", replayed, by_expr, diverged, alike);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 4 1 4\n");
}

// 18.13.3: the RNG of a process is seeded with the srandom() method of the
// process (9.7), so four $urandom draws after p.srandom(55) are replayed in
// full after a second p.srandom(55) though an object was seeded and drawn
// from between the two, the object's RNG being its own (18.14), and changed
// by p.srandom(56).
TEST(SrandomRun, TheProcessSeedIsItsOwn) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class Packet;\n"
      "    rand bit [15:0] payload;\n"
      "  endclass\n"
      "  Packet a;\n"
      "  process p;\n"
      "  int i, k, replayed = 0, diverged = 0;\n"
      "  int unsigned ua[4], ub[4];\n"
      "  initial begin\n"
      "    a = new;\n"
      "    p = process::self();\n"
      "    p.srandom(55);\n"
      "    for (i = 0; i < 4; i++) ua[i] = $urandom;\n"
      "    p.srandom(55);\n"
      "    a.srandom(9);\n"
      "    for (i = 0; i < 4; i++) k = a.randomize();\n"
      "    for (i = 0; i < 4; i++) ub[i] = $urandom;\n"
      "    for (i = 0; i < 4; i++) if (ua[i] == ub[i]) replayed++;\n"
      "    p.srandom(56);\n"
      "    for (i = 0; i < 4; i++) ub[i] = $urandom;\n"
      "    for (i = 0; i < 4; i++) if (ua[i] != ub[i]) diverged = 1;\n"
      "    $display(\"%0d %0d\", replayed, diverged);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 1\n");
}

}  // namespace
