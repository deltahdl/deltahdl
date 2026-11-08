#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

const char* const kPacket =
    "class Packet;\n"
    "  rand bit mode;\n"
    "  rand int length;\n"
    "  constraint deflt {\n"
    "    soft length inside {32, 1024};\n"
    "    soft mode -> length == 1024;\n"
    "  }\n"
    "endclass\n";

TEST(SoftConstraintsRun, TheContradictedSizeIsDiscardedAndModeStaysZero) {
  SimFixture f;
  std::string out =
      RunCapture(std::string(kPacket) +
                     "module t;\n"
                     "  int ok = 0, held = 0, zeros = 0;\n"
                     "  initial begin\n"
                     "    static Packet p = new;\n"
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

TEST(SoftConstraintsRun, BothPreferencesAreDiscardedUnderModeOne) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kPacket) +
          "module t;\n"
          "  int ok = 0, held = 0, ones = 0;\n"
          "  initial begin\n"
          "    static Packet p = new;\n"
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
      "    static Strict s = new;\n"
      "    against = s.randomize() with { length == 1512; };\n"
      "    alone = s.randomize();\n"
      "    $display(\"%0d %0d\", against, alone);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 1\n");
}

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
      "    static Preferred q = new;\n"
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
