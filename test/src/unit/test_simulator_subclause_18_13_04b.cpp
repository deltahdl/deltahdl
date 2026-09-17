#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// 18.13.4: get_randstate() retrieves the current internal state of an
// object's RNG as a string, so the string has a length, two retrievals with
// no draw between agree, an object seeded alike holds the same state, four
// draws move the state while the other object's is kept, and the retrieved
// state installed again with set_randstate() replays all four draws, as the
// design test/src/e2e/get_randstate_method.sv runs it.
TEST(GetRandstateRun, TheStateOfAnObjectIsReadMovedAndReplayed) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class Packet;\n"
      "    rand bit [15:0] payload;\n"
      "  endclass\n"
      "  Packet a, b;\n"
      "  string s1, s2, s3;\n"
      "  int i, k, has_length, agree, alike, moved, kept, replayed = 0;\n"
      "  bit [15:0] sa[4], sb[4];\n"
      "  initial begin\n"
      "    a = new; b = new;\n"
      "    a.srandom(7); b.srandom(7);\n"
      "    s1 = a.get_randstate();\n"
      "    s2 = a.get_randstate();\n"
      "    s3 = b.get_randstate();\n"
      "    has_length = s1.len() > 0;\n"
      "    agree = s1 == s2;\n"
      "    alike = s1 == s3;\n"
      "    for (i = 0; i < 4; i++) begin k = a.randomize(); sa[i] = a.payload; "
      "end\n"
      "    s2 = a.get_randstate();\n"
      "    moved = s1 != s2;\n"
      "    s2 = b.get_randstate();\n"
      "    kept = s3 == s2;\n"
      "    a.set_randstate(s1);\n"
      "    for (i = 0; i < 4; i++) begin k = a.randomize(); sb[i] = a.payload; "
      "end\n"
      "    for (i = 0; i < 4; i++) if (sa[i] == sb[i]) replayed++;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", has_length, agree, alike, "
      "moved,\n"
      "             kept, replayed);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1 1 1 4\n");
}

// 18.13.4: the state of the RNG associated with a process is retrieved with
// the get_randstate() method of the process (9.7): the string has a length,
// two retrievals agree, four $urandom draws move it, and the retrieved state
// installed again replays all four.
TEST(GetRandstateRun, TheStateOfTheProcessIsReadMovedAndReplayed) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  process p;\n"
      "  string s1, s2;\n"
      "  int i, has_length, agree, moved, replayed = 0;\n"
      "  int unsigned ua[4], ub[4];\n"
      "  initial begin\n"
      "    p = process::self();\n"
      "    s1 = p.get_randstate();\n"
      "    s2 = p.get_randstate();\n"
      "    has_length = s1.len() > 0;\n"
      "    agree = s1 == s2;\n"
      "    for (i = 0; i < 4; i++) ua[i] = $urandom;\n"
      "    s2 = p.get_randstate();\n"
      "    moved = s1 != s2;\n"
      "    p.set_randstate(s1);\n"
      "    for (i = 0; i < 4; i++) ub[i] = $urandom;\n"
      "    for (i = 0; i < 4; i++) if (ua[i] == ub[i]) replayed++;\n"
      "    $display(\"%0d %0d %0d %0d\", has_length, agree, moved, replayed);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1 4\n");
}

}  // namespace
