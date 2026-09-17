#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// The clause's Packet: a mode and a length whose legal sizes, and whose
// length under mode 1, are preferences rather than requirements.
const char* const kPacket =
    "class Packet;\n"
    "  rand bit mode;\n"
    "  rand int length;\n"
    "  constraint deflt {\n"
    "    soft length inside {32, 1024};\n"
    "    soft mode -> length == 1024;\n"
    "  }\n"
    "endclass\n";

// 18.5.13: the clause's first call, randomize() with length == 1512. The
// hard length contradicts the soft size, which is discarded, while the soft
// implication can still hold and does, so over 32 draws the length is 1512
// and mode randomizes to 0 on every one, as the design
// test/src/e2e/soft_constraints.sv runs it.
TEST(SoftConstraintsRun, TheContradictedSizeIsDiscardedAndModeStaysZero) {
  SimFixture f;
  std::string out =
      RunCapture(std::string(kPacket) +
                     "module t;\n"
                     "  int ok = 0, held = 0, zeros = 0;\n"
                     "  initial begin\n"
                     "    Packet p = new;\n"
                     "    repeat (32) begin\n"
                     "      if (p.randomize() with { length == 1512; }) ok++;\n"
                     "      if (p.length == 1512) held++;\n"
                     "      if (!p.mode) zeros++;\n"
                     "    end\n"
                     "    $display(\"%0d %0d %0d\", ok, held, zeros);\n"
                     "  end\n"
                     "endmodule\n",
                 f);
  EXPECT_EQ(out, "32 32 32\n");
}

// 18.5.13: the clause's second call, with length == 1512 and mode == 1,
// which contradicts the soft implication as well: both preferences are
// discarded, treated as true, and every draw solves with mode 1 at 1512.
TEST(SoftConstraintsRun, BothPreferencesAreDiscardedUnderModeOne) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kPacket) +
          "module t;\n"
          "  int ok = 0, held = 0, ones = 0;\n"
          "  initial begin\n"
          "    Packet p = new;\n"
          "    repeat (32) begin\n"
          "      if (p.randomize() with { length == 1512; mode == 1; }) ok++;\n"
          "      if (p.length == 1512) held++;\n"
          "      if (p.mode) ones++;\n"
          "    end\n"
          "    $display(\"%0d %0d %0d\", ok, held, ones);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32 32\n");
}

// 18.5.13: the same size constraint not defined as soft is a hard
// constraint the solver shall satisfy or fail, so the call with length ==
// 1512 fails where the call without it solves.
TEST(SoftConstraintsRun, TheHardSizeFailsTheContradictingCall) {
  SimFixture f;
  std::string out = RunCapture(
      "class Strict;\n"
      "  rand bit mode;\n"
      "  rand int length;\n"
      "  constraint sizes { length inside {32, 1024}; }\n"
      "endclass\n"
      "module t;\n"
      "  int against, alone;\n"
      "  initial begin\n"
      "    Strict s = new;\n"
      "    against = s.randomize() with { length == 1512; };\n"
      "    alone = s.randomize();\n"
      "    $display(\"%0d %0d\", against, alone);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 1\n");
}

// 18.5.13: a discarded soft constraint is replaced by true and has no
// effect on the solution distribution: a soft v == 3 overridden by an
// inline v != 3 leaves the 4-bit v spread over its other values, at least
// eight distinct ones over 64 draws, and never 3.
TEST(SoftConstraintsRun, ADiscardedPreferenceLeavesTheDistributionAlone) {
  SimFixture f;
  std::string out = RunCapture(
      "class Preferred;\n"
      "  rand bit [3:0] v;\n"
      "  constraint pref { soft v == 3; }\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0, distinct = 0;\n"
      "  bit [15:0] seen = 0;\n"
      "  initial begin\n"
      "    Preferred q = new;\n"
      "    repeat (64) begin\n"
      "      void'(q.randomize() with { v != 3; });\n"
      "      if (q.v == 3) held++;\n"
      "      seen = seen | (16'd1 << q.v);\n"
      "    end\n"
      "    for (int j = 0; j < 16; j++) if (seen[j]) distinct++;\n"
      "    $display(\"%0d %0d\", held, distinct >= 8);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 1\n");
}

}  // namespace
