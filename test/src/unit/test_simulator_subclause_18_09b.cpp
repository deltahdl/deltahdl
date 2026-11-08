#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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

TEST(ConstraintModeRun, TheToggleTurnsTheBlockOffAndOnForTheCall) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kPacket) +
          "  int wide = 0, above = 0, off_state, on_state;\n"
          "  initial begin\n"
          "    static Packet p = new;\n"
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

TEST(ConstraintModeRun, TheObjectCallTurnsEveryBlockOff) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kPacket) +
          "  int wide = 0, first_a, first_b;\n"
          "  initial begin\n"
          "    static Packet p = new;\n"
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
