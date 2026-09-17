#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

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

// 18.8: an inactive variable is not randomized and its value is a state
// variable to the solver: with dest_value turned off at 41, every one of
// 32 calls keeps it and draws source_value as 40, the one value the
// constraint admits, as the design test/src/e2e/rand_mode.sv runs it.
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

}  // namespace
