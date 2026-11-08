#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char* const kPacket =
    "class Packet;\n"
    "  rand integer source_value, dest_value;\n"
    "  rand bit [7:0] arr[4];\n"
    "  constraint follows { dest_value == source_value + 1; }\n"
    "endclass\n";

TEST(RandModeRun, AnInactiveVariableIsAStateVariableToTheSolver) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kPacket) +
          "module t;\n"
          "  int held = 0;\n"
          "  initial begin\n"
          "    static Packet p = new;\n"
          "    p.dest_value = 41;\n"
          "    p.dest_value.rand_mode(0);\n"
          "    repeat (32) begin\n"
          "      void'(p.randomize());\n"
          "      if (p.dest_value == 41 && p.source_value == 40) held++;\n"
          "    end\n"
          "    $display(\"%0d %0d\", held, p.dest_value.rand_mode());\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "32 0\n");
}

TEST(RandModeRun, TheObjectCallTurnsEveryVariableOff) {
  SimFixture f;
  std::string out =
      RunCapture(std::string(kPacket) +
                     "module t;\n"
                     "  int at_start, ret;\n"
                     "  initial begin\n"
                     "    static Packet packet_a = new;\n"
                     "    at_start = packet_a.dest_value.rand_mode();\n"
                     "    packet_a.rand_mode(0);\n"
                     "    packet_a.source_value.rand_mode(1);\n"
                     "    ret = packet_a.dest_value.rand_mode();\n"
                     "    $display(\"%0d %0d %0d %0d\", at_start, ret,\n"
                     "             packet_a.source_value.rand_mode(), "
                     "packet_a.arr[1].rand_mode());\n"
                     "  end\n"
                     "endmodule\n",
                 f);
  EXPECT_EQ(out, "1 0 1 0\n");
}

TEST(RandModeRun, AnArrayElementIsNamedByItsIndex) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kPacket) +
          "module t;\n"
          "  int held = 0, moved = 0;\n"
          "  initial begin\n"
          "    static Packet p = new;\n"
          "    p.arr[2] = 9;\n"
          "    p.arr[2].rand_mode(0);\n"
          "    repeat (32) begin\n"
          "      void'(p.randomize());\n"
          "      if (p.arr[2] == 9) held++;\n"
          "      if (p.arr[0] != 9 || p.arr[1] != 9 || p.arr[3] != 9) "
          "moved++;\n"
          "    end\n"
          "    p.arr[2].rand_mode(1);\n"
          "    p.arr.rand_mode(0);\n"
          "    $display(\"%0d %0d %0d %0d\", held, moved > 0, "
          "p.arr[2].rand_mode(),\n"
          "             p.arr[0].rand_mode());\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "32 1 0 0\n");
}

TEST(RandModeRun, AStaticVariablesModeIsSharedByEveryInstance) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  static rand bit [7:0] s;\n"
      "  rand bit [7:0] n;\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static C a = new, b = new;\n"
      "    a.s = 99;\n"
      "    a.s.rand_mode(0);\n"
      "    a.n.rand_mode(0);\n"
      "    void'(b.randomize());\n"
      "    $display(\"%0d %0d %0d\", b.s.rand_mode(), b.s == 99,\n"
      "             b.n.rand_mode());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 1 1\n");
}

TEST(RandModeRun, ACallsResultIsTheObjectAndIsCalledOnce) {
  SimFixture f;
  std::string out = RunCapture(
      "class K;\n"
      "  rand bit [3:0] x;\n"
      "  rand bit [3:0] a[2];\n"
      "endclass\n"
      "module t;\n"
      "  int calls = 0, r;\n"
      "  K k = new;\n"
      "  function K pk();\n"
      "    calls++;\n"
      "    return k;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    pk().x.rand_mode(0);\n"
      "    pk().a[1].rand_mode(0);\n"
      "    r = pk().x.rand_mode();\n"
      "    $display(\"%0d %0d %0d %0d\", calls, r, k.a[1].rand_mode(),\n"
      "             k.a[0].rand_mode());\n"
      "    pk().rand_mode(0);\n"
      "    $display(\"%0d %0d\", calls, k.a[0].rand_mode());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 0 0 1\n4 0\n");
}

TEST(RandModeRun, AnArrayElementIsTheObjectItHolds) {
  SimFixture f;
  std::string out = RunCapture(
      "class K;\n"
      "  rand bit [3:0] x;\n"
      "  rand bit [3:0] a[2];\n"
      "endclass\n"
      "module t;\n"
      "  K ks[2];\n"
      "  K first, second;\n"
      "  initial begin\n"
      "    ks[0] = new;\n"
      "    ks[1] = new;\n"
      "    first = ks[0];\n"
      "    second = ks[1];\n"
      "    ks[1].x.rand_mode(0);\n"
      "    ks[1].a[0].rand_mode(0);\n"
      "    ks[0].rand_mode(0);\n"
      "    $display(\"%0d %0d %0d %0d %0d\", second.x.rand_mode(),\n"
      "             second.a[0].rand_mode(), ks[1].a[1].rand_mode(),\n"
      "             first.a[1].rand_mode(), ks[1].x.rand_mode());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 0 1 0 0\n");
}

TEST(RandModeRun, AHandlePropertyIsTheObjectUnlessItIsRandom) {
  SimFixture f;
  std::string out = RunCapture(
      "class K;\n"
      "  rand bit [3:0] x, y;\n"
      "endclass\n"
      "class H;\n"
      "  K k;\n"
      "  rand K r;\n"
      "  function new();\n"
      "    k = new;\n"
      "    r = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int calls = 0;\n"
      "  H h = new;\n"
      "  function H ph();\n"
      "    calls++;\n"
      "    return h;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    ph().k.rand_mode(0);\n"
      "    ph().r.rand_mode(0);\n"
      "    ph().r.y.rand_mode(0);\n"
      "    $display(\"%0d %0d %0d %0d %0d\", calls, h.k.x.rand_mode(),\n"
      "             h.r.rand_mode(), h.r.x.rand_mode(), h.r.y.rand_mode());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 0 0 1 0\n");
}

TEST(RandModeRun, ACallsNullResultIsReported) {
  SimFixture f;
  std::string out = RunCapture(
      "class K;\n"
      "  rand bit [3:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int calls = 0, r = 7;\n"
      "  function K pn();\n"
      "    calls++;\n"
      "    return null;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    pn().x.rand_mode(0);\n"
      "    r = pn().x.rand_mode();\n"
      "    $display(\"%0d %0d\", calls, r);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 0\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'rand_mode' called through a null handle",
                            11, "8.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'rand_mode' called through a null handle",
                            12, "8.4"));
}

TEST(RandModeRun, AStructureMemberIsNamedByItsMember) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand struct { rand bit [3:0] a; rand bit [3:0] b; } s;\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.s.a = 5;\n"
      "    c.s.a.rand_mode(0);\n"
      "    repeat (8) void'(c.randomize());\n"
      "    $display(\"%0d %0d\", c.s.a, c.s.a.rand_mode());\n"
      "    c.s.rand_mode(1);\n"
      "    $display(\"%0d\", c.s.a.rand_mode());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5 0\n1\n");
}

TEST(RandModeRun, AnElementOfAMultidimensionalArrayIsNamedByItsIndices) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] arr[2][3];\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.arr[1][2] = 7;\n"
      "    c.arr[1][2].rand_mode(0);\n"
      "    repeat (8) void'(c.randomize());\n"
      "    $display(\"%0d %0d\", c.arr[1][2], c.arr[1][2].rand_mode());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "7 0\n");
}

TEST(RandModeRun, ASubarrayTurnsEveryElementOfItOff) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] arr[2][3];\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    foreach (c.arr[i, j]) c.arr[i][j] = 7;\n"
      "    c.arr[1].rand_mode(0);\n"
      "    repeat (8) void'(c.randomize());\n"
      "    $display(\"%0d %0d %0d %0d\", c.arr[1][0], c.arr[1][1], "
      "c.arr[1][2],\n"
      "             c.arr[1][0].rand_mode());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "7 7 7 0\n");
}

}  // namespace
