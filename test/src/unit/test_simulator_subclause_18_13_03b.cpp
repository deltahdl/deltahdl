#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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

TEST(SrandomRun, AnArrayElementIsSeeded) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class Packet;\n"
      "    rand bit [15:0] payload;\n"
      "  endclass\n"
      "  Packet arr[2];\n"
      "  int i, k, same = 0;\n"
      "  initial begin\n"
      "    arr[0] = new; arr[1] = new;\n"
      "    arr[0].srandom(5); arr[1].srandom(5);\n"
      "    for (i = 0; i < 4; i++) begin\n"
      "      k = arr[0].randomize(); k = arr[1].randomize();\n"
      "      if (arr[0].payload == arr[1].payload) same++;\n"
      "    end\n"
      "    $display(\"%0d\", same);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

TEST(SrandomRun, EveryWayOfReachingTheObjectSeedsIt) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class P;\n"
      "    rand bit [15:0] v;\n"
      "    function new(int s = -1);\n"
      "      if (s >= 0) srandom(s);\n"
      "    endfunction\n"
      "    function void seed_this(int s); this.srandom(s); endfunction\n"
      "    function void seed_bare(int s); srandom(s); endfunction\n"
      "  endclass\n"
      "  class D extends P;\n"
      "    function new(int s);\n"
      "      super.new();\n"
      "      this.srandom(s);\n"
      "    endfunction\n"
      "  endclass\n"
      "  function automatic bit [63:0] four(P p);\n"
      "    four = 0;\n"
      "    repeat (4) begin\n"
      "      void'(p.randomize());\n"
      "      four = {four[47:0], p.v};\n"
      "    end\n"
      "  endfunction\n"
      "  function automatic void seed_through(P p, int s); p.srandom(s); "
      "endfunction\n"
      "  bit [63:0] want;\n"
      "  initial begin\n"
      "    static P a = new;\n"
      "    static D d = new(7);\n"
      "    a.srandom(7);\n"
      "    want = four(a);\n"
      "    a.seed_this(7);\n"
      "    $write(\"%0d\", four(a) == want);\n"
      "    $write(\" %0d\", four(d) == want);\n"
      "    seed_through(a, 7);\n"
      "    $write(\" %0d\", four(a) == want);\n"
      "    $display(\"\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1\n");
}

TEST(SrandomRun, DISABLED_AnUnqualifiedCallSeedsTheEnclosingObject) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class P;\n"
      "    rand bit [15:0] v;\n"
      "    function new(int s = -1);\n"
      "      if (s >= 0) srandom(s);\n"
      "    endfunction\n"
      "    function void seed_this(int s); this.srandom(s); endfunction\n"
      "    function void seed_bare(int s); srandom(s); endfunction\n"
      "  endclass\n"
      "  class D extends P;\n"
      "    function new(int s);\n"
      "      super.new();\n"
      "      this.srandom(s);\n"
      "    endfunction\n"
      "  endclass\n"
      "  function automatic bit [63:0] four(P p);\n"
      "    four = 0;\n"
      "    repeat (4) begin\n"
      "      void'(p.randomize());\n"
      "      four = {four[47:0], p.v};\n"
      "    end\n"
      "  endfunction\n"
      "  function automatic void seed_through(P p, int s); p.srandom(s); "
      "endfunction\n"
      "  bit [63:0] want;\n"
      "  initial begin\n"
      "    static P a = new;\n"
      "    static P b = new(7);\n"
      "    a.srandom(7);\n"
      "    want = four(a);\n"
      "    $write(\"%0d\", four(b) == want);\n"
      "    a.seed_bare(7);\n"
      "    $write(\" %0d\", four(a) == want);\n"
      "    $display(\"\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1\n");
}

}  // namespace
