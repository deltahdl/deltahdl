#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The clause's Packet, its dest_value held one above its source_value,
// beside an unpacked array of four bytes.
const char* const kPacket =
    "class Packet;\n"
    "  rand integer source_value, dest_value;\n"
    "  rand bit [7:0] arr[4];\n"
    "  constraint follows { dest_value == source_value + 1; }\n"
    "endclass\n";

// 18.8: the solver leaves an inactive variable alone and reads its value as
// state: with dest_value turned off at 41, every one of 32 calls keeps it and
// draws source_value as 40, the one value the constraint admits, as the design
// test/src/e2e/rand_mode.sv runs it.
TEST(RandModeRun, AnInactiveVariableIsAStateVariableToTheSolver) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kPacket) +
          "module t;\n"
          "  int held = 0;\n"
          "  initial begin\n"
          "    Packet p = new;\n"
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

// 18.8: the clause's example. Every variable is active to begin with; the
// call on the object turns all of them off, source_value alone is turned
// back on, and the nonvoid form reports dest_value inactive.
TEST(RandModeRun, TheObjectCallTurnsEveryVariableOff) {
  SimFixture f;
  std::string out =
      RunCapture(std::string(kPacket) +
                     "module t;\n"
                     "  int at_start, ret;\n"
                     "  initial begin\n"
                     "    Packet packet_a = new;\n"
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

// 18.8: for an unpacked array variable rand_mode() names an element by its
// index: arr[2] turned off at 9 keeps it over 32 calls while the other
// elements are drawn, and the array turned off as a whole afterwards
// covers the element's own state.
TEST(RandModeRun, AnArrayElementIsNamedByItsIndex) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kPacket) +
          "module t;\n"
          "  int held = 0, moved = 0;\n"
          "  initial begin\n"
          "    Packet p = new;\n"
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

// §18.8: the rand_mode state of a static random variable is static too: set
// inactive through a, it is inactive through b, whose randomize() then holds
// the 99 written through a; a nonstatic variable beside it keeps a state per
// instance.
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

// §18.8 with §8.6: rand_mode() acts on the object a call returns, through a
// variable of it, an element of its array or the object as a whole, and
// §11.3.1 has the call run once for each: three calls turn off x and a[1]
// and read x back off, leaving a[0] on, and a fourth turns a[0] off too.
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

// §18.8 with §8.6: an element of an array of handles is the object it holds,
// so the calls through ks[1] and ks[0] change the modes read through the
// handles first and second, and the queries through ks[1] answer its own
// object's modes.
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

// §18.8: through a call's result, ph().r names the random variable r of the
// object, whose mode alone the call turns off, while ph().k, no random
// variable, is the handle to an object of its own, every variable of which
// the call turns off; ph() runs once per call (§11.3.1).
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

// §18.8 with §8.4: a call returning the null handle yields no object whose
// variable the call could reach, so both forms are reported as calls through a
// null handle, the query answers 0, and the call runs once for each.
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

}  // namespace
