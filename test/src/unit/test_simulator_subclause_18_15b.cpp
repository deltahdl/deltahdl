#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

const char* const kPacket =
    "  class Packet;\n"
    "    rand bit [15:0] header;\n"
    "    function new(int seed, bit draw = 0);\n"
    "      this.srandom(seed);\n"
    "      if (draw) void'(this.randomize());\n"
    "    endfunction\n"
    "  endclass\n";

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
