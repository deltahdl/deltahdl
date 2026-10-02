#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The clause's Packet, its source_value above twice a state m of 100 under
// filter1, beside a ceiling below 1000, and the clause's toggle_rand.
const char* const kPacket =
    "class Packet;\n"
    "  rand integer source_value;\n"
    "  integer m = 100;\n"
    "  constraint filter1 { source_value > 2 * m; }\n"
    "  constraint ceiling { source_value < 1000; }\n"
    "endclass\n"
    "module t;\n"
    "  function integer toggle_rand(Packet p);\n"
    "    if (p.filter1.constraint_mode())\n"
    "      p.filter1.constraint_mode(0);\n"
    "    else\n"
    "      p.filter1.constraint_mode(1);\n"
    "    toggle_rand = p.randomize();\n"
    "  endfunction\n";

// 18.9: the clause's toggle_rand deactivates filter1 where it is active
// and activates it where it is not, then randomizes: toggled from on, the
// block is not considered and source_value falls at or below 200 in some
// of 32 calls; toggled from off, every call draws it above 200 below 1000,
// as the design test/src/e2e/constraint_mode.sv runs it.
TEST(ConstraintModeRun, TheToggleTurnsTheBlockOffAndOnForTheCall) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kPacket) +
          "  int wide = 0, above = 0, off_state, on_state;\n"
          "  initial begin\n"
          "    Packet p = new;\n"
          "    repeat (32) begin\n"
          "      p.filter1.constraint_mode(1);\n"
          "      void'(toggle_rand(p));\n"
          "      if (p.source_value <= 200) wide++;\n"
          "    end\n"
          "    off_state = p.filter1.constraint_mode();\n"
          "    repeat (32) begin\n"
          "      p.filter1.constraint_mode(0);\n"
          "      void'(toggle_rand(p));\n"
          "      if (p.source_value > 200 && p.source_value < 1000) above++;\n"
          "    end\n"
          "    on_state = p.filter1.constraint_mode();\n"
          "    $display(\"%0d %0d %0d %0d\", wide > 0, off_state, above, "
          "on_state);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "1 0 32 1\n");
}

// 18.9: all constraints are initially active, and the call on the object
// with no block named applies to every block: both read active before any
// call and inactive after, and source_value then ranges outside both
// bounds in some of 32 calls.
TEST(ConstraintModeRun, TheObjectCallTurnsEveryBlockOff) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kPacket) +
          "  int wide = 0, first_a, first_b;\n"
          "  initial begin\n"
          "    Packet p = new;\n"
          "    first_a = p.filter1.constraint_mode();\n"
          "    first_b = p.ceiling.constraint_mode();\n"
          "    p.constraint_mode(0);\n"
          "    repeat (32) begin\n"
          "      void'(p.randomize());\n"
          "      if (p.source_value >= 1000 || p.source_value <= 200) wide++;\n"
          "    end\n"
          "    $display(\"%0d %0d %0d %0d %0d\", first_a, first_b,\n"
          "             p.filter1.constraint_mode(), "
          "p.ceiling.constraint_mode(), wide > 0);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 0 0 1\n");
}

// §18.9 with §8.6: constraint_mode() acts on the object a call returns,
// through a block of it or the object as a whole, and §11.3.1 has the call
// run once for each: two calls turn lo off and read it back off, leaving hi
// on, and a third turns hi off too.
TEST(ConstraintModeRun, ACallsResultIsTheObjectAndIsCalledOnce) {
  SimFixture f;
  std::string out = RunCapture(
      "class K;\n"
      "  rand bit [3:0] x;\n"
      "  constraint lo { x > 2; }\n"
      "  constraint hi { x < 9; }\n"
      "endclass\n"
      "module t;\n"
      "  int calls = 0, r;\n"
      "  K k = new;\n"
      "  function K pk();\n"
      "    calls++;\n"
      "    return k;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    pk().lo.constraint_mode(0);\n"
      "    r = pk().lo.constraint_mode();\n"
      "    $display(\"%0d %0d %0d\", calls, r, k.hi.constraint_mode());\n"
      "    pk().constraint_mode(0);\n"
      "    $display(\"%0d %0d\", calls, k.hi.constraint_mode());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 0 1\n3 0\n");
}

// §18.9 with §8.6: an element of an array of handles is the object it holds,
// so the calls through ks[1] and ks[0] change the modes read through the
// handles first and second, and the queries through ks[1] answer its own
// object's modes.
TEST(ConstraintModeRun, AnArrayElementIsTheObjectItHolds) {
  SimFixture f;
  std::string out = RunCapture(
      "class K;\n"
      "  rand bit [3:0] x;\n"
      "  constraint lo { x > 2; }\n"
      "  constraint hi { x < 9; }\n"
      "endclass\n"
      "module t;\n"
      "  K ks[2];\n"
      "  K first, second;\n"
      "  initial begin\n"
      "    ks[0] = new;\n"
      "    ks[1] = new;\n"
      "    first = ks[0];\n"
      "    second = ks[1];\n"
      "    ks[1].lo.constraint_mode(0);\n"
      "    ks[0].constraint_mode(0);\n"
      "    $display(\"%0d %0d %0d %0d\", second.lo.constraint_mode(),\n"
      "             ks[1].hi.constraint_mode(), first.hi.constraint_mode(),\n"
      "             ks[1].lo.constraint_mode());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 1 0 0\n");
}

// §18.9 with §8.4: a call returning the null handle yields no object whose
// block the call could reach, so both forms are reported as calls through a
// null handle, the query answers 0, and the call runs once for each.
TEST(ConstraintModeRun, ACallsNullResultIsReported) {
  SimFixture f;
  std::string out = RunCapture(
      "class K;\n"
      "  rand bit [3:0] x;\n"
      "  constraint lo { x > 2; }\n"
      "endclass\n"
      "module t;\n"
      "  int calls = 0, r = 7;\n"
      "  function K pn();\n"
      "    calls++;\n"
      "    return null;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    pn().lo.constraint_mode(0);\n"
      "    r = pn().lo.constraint_mode();\n"
      "    $display(\"%0d %0d\", calls, r);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 0\n");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "method 'constraint_mode' called through a null handle", 12, "8.4"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "method 'constraint_mode' called through a null handle", 13, "8.4"));
}

}  // namespace
