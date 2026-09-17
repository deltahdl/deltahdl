#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// The clause's Packet, its new(seed) seeding the object's RNG with
// this.srandom(seed) and, when asked, randomizing the object there too.
const char* const kPacket =
    "  class Packet;\n"
    "    rand bit [15:0] header;\n"
    "    function new(int seed, bit draw = 0);\n"
    "      this.srandom(seed);\n"
    "      if (draw) void'(this.randomize());\n"
    "    endfunction\n"
    "  endclass\n";

// 18.15: an object's RNG can be seeded in a class method, and is used by its
// randomize() alone, so two Packets whose new() seeds them with 200 draw the
// same four values though created at different points of the thread, and a
// $urandom and a $random before each draw change nothing; and srandom() in
// new() sets the seed before any member is randomized, so a Packet that
// randomizes itself inside new() holds the first draw of one that does not,
// as the design test/src/e2e/manually_seeding_randomize.sv runs it.
TEST(ManuallySeedingRandomizeRun, SeedingInNewSelectsTheDrawsOfEveryPacket) {
  SimFixture f;
  std::string out = RunCapture(
      std::string("module t;\n") + kPacket +
          "  Packet p, q;\n"
          "  process pr;\n"
          "  integer z;\n"
          "  int unsigned k;\n"
          "  bit [15:0] h1[4], h2[4], h3[4];\n"
          "  int i, alike = 0, unmoved = 0, in_new;\n"
          "  initial begin\n"
          "    pr = process::self();\n"
          "    pr.srandom(9);\n"
          "    p = new(200);\n"
          "    for (i = 0; i < 4; i++) begin void'(p.randomize()); h1[i] = "
          "p.header; end\n"
          "    for (i = 0; i < 5; i++) k = $urandom;\n"
          "    q = new(200);\n"
          "    for (i = 0; i < 4; i++) begin void'(q.randomize()); h2[i] = "
          "q.header; end\n"
          "    for (i = 0; i < 4; i++) if (h1[i] == h2[i]) alike++;\n"
          "    p = new(200);\n"
          "    for (i = 0; i < 4; i++) begin k = $urandom; z = $random; "
          "void'(p.randomize()); h3[i] = p.header; end\n"
          "    for (i = 0; i < 4; i++) if (h1[i] == h3[i]) unmoved++;\n"
          "    q = new(200, 1);\n"
          "    in_new = q.header == h1[0];\n"
          "    $display(\"%0d %0d %0d\", alike, unmoved, in_new);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "4 4 1\n");
}

// 18.15: an object's RNG can be seeded from outside the class with srandom(),
// so a Packet re-seeded with 300 draws the four values of one created with
// 300; and an object is seeded at creation with the next value of the
// creating thread's RNG, so a Plain object without a seeding constructor
// draws as one seeded by hand with that value, as the design
// test/src/e2e/manually_seeding_randomize.sv runs it.
TEST(ManuallySeedingRandomizeRun,
     ExternalAndHierarchicalSeedingSelectTheDraws) {
  SimFixture f;
  std::string out = RunCapture(
      std::string("module t;\n") + kPacket +
          "  class Plain;\n"
          "    rand bit [15:0] header;\n"
          "  endclass\n"
          "  Packet p, r;\n"
          "  Plain a, b;\n"
          "  process pr;\n"
          "  int unsigned seedv;\n"
          "  bit [15:0] h1[4], h2[4];\n"
          "  int i, external = 0, hierarchical = 0;\n"
          "  initial begin\n"
          "    pr = process::self();\n"
          "    pr.srandom(9);\n"
          "    p = new(200);\n"
          "    p.srandom(300);\n"
          "    for (i = 0; i < 4; i++) begin void'(p.randomize()); h1[i] = "
          "p.header; end\n"
          "    r = new(300);\n"
          "    for (i = 0; i < 4; i++) begin void'(r.randomize()); h2[i] = "
          "r.header; end\n"
          "    for (i = 0; i < 4; i++) if (h1[i] == h2[i]) external++;\n"
          "    pr.srandom(9);\n"
          "    a = new;\n"
          "    for (i = 0; i < 4; i++) begin void'(a.randomize()); h1[i] = "
          "a.header; end\n"
          "    pr.srandom(9);\n"
          "    seedv = $urandom;\n"
          "    b = new;\n"
          "    b.srandom(seedv);\n"
          "    for (i = 0; i < 4; i++) begin void'(b.randomize()); h2[i] = "
          "b.header; end\n"
          "    for (i = 0; i < 4; i++) if (h1[i] == h2[i]) hierarchical++;\n"
          "    $display(\"%0d %0d\", external, hierarchical);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "4 4\n");
}

}  // namespace
