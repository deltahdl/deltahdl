#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// 18.13.5: set_randstate() sets an object's RNG internal state with the given
// value, so a state read from an object and installed on it again replays
// the four draws that followed the read, installed on another object it
// makes that object continue the stream in all four draws, the installed
// state reads back, and a third object's state is kept, as the design
// test/src/e2e/set_randstate_method.sv runs it.
TEST(SetRandstateRun, TheStateInstalledOnAnObjectSetsWhatItDrawsNext) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class Packet;\n"
      "    rand bit [15:0] payload;\n"
      "  endclass\n"
      "  Packet a, b, c;\n"
      "  string s, t;\n"
      "  int i, k, replayed = 0, continued = 0, reads_back, kept;\n"
      "  bit [15:0] sa[4], sr[4], sb[4];\n"
      "  initial begin\n"
      "    a = new; b = new; c = new;\n"
      "    a.srandom(3); b.srandom(8); c.srandom(8);\n"
      "    for (i = 0; i < 2; i++) k = a.randomize();\n"
      "    s = a.get_randstate();\n"
      "    for (i = 0; i < 4; i++) begin k = a.randomize(); sa[i] = a.payload; "
      "end\n"
      "    a.set_randstate(s);\n"
      "    for (i = 0; i < 4; i++) begin k = a.randomize(); sr[i] = a.payload; "
      "end\n"
      "    for (i = 0; i < 4; i++) if (sa[i] == sr[i]) replayed++;\n"
      "    for (i = 0; i < 2; i++) k = b.randomize();\n"
      "    for (i = 0; i < 2; i++) k = c.randomize();\n"
      "    t = c.get_randstate();\n"
      "    b.set_randstate(s);\n"
      "    for (i = 0; i < 4; i++) begin k = b.randomize(); sb[i] = b.payload; "
      "end\n"
      "    for (i = 0; i < 4; i++) if (sa[i] == sb[i]) continued++;\n"
      "    b.set_randstate(s);\n"
      "    reads_back = b.get_randstate() == s;\n"
      "    kept = c.get_randstate() == t;\n"
      "    $display(\"%0d %0d %0d %0d\", replayed, continued, reads_back, "
      "kept);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 4 1 1\n");
}

// 18.13.5 via 9.7: the state of the RNG associated with a process is set with
// the set_randstate() of the process, so a state read from the running
// process and installed again replays the four $urandom draws that followed
// the read, installed on a forked thread it makes the thread continue the
// stream in all four draws, and the install on the thread does not set the
// parent: the fork seeds the thread with the parent's next value (18.14.1),
// so the parent is left where a fork without the install leaves it, as the
// design test/src/e2e/set_randstate_method.sv runs it.
TEST(SetRandstateRun, TheStateInstalledOnTheProcessOrAThreadSetsWhatItDraws) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  process p;\n"
      "  string s, t, t2;\n"
      "  int i, k, replayed = 0, continued = 0, kept;\n"
      "  int unsigned ua[4], ur[4], uc[4];\n"
      "  initial begin\n"
      "    p = process::self();\n"
      "    for (i = 0; i < 2; i++) k = $urandom;\n"
      "    s = p.get_randstate();\n"
      "    for (i = 0; i < 4; i++) ua[i] = $urandom;\n"
      "    p.set_randstate(s);\n"
      "    for (i = 0; i < 4; i++) ur[i] = $urandom;\n"
      "    for (i = 0; i < 4; i++) if (ua[i] == ur[i]) replayed++;\n"
      "    t = p.get_randstate();\n"
      "    fork\n"
      "      begin\n"
      "        process q = process::self();\n"
      "        q.set_randstate(s);\n"
      "        for (int j = 0; j < 4; j++) uc[j] = $urandom;\n"
      "      end\n"
      "    join\n"
      "    for (i = 0; i < 4; i++) if (ua[i] == uc[i]) continued++;\n"
      "    t2 = p.get_randstate();\n"
      "    p.set_randstate(t);\n"
      "    fork\n"
      "      begin\n"
      "        for (int j = 0; j < 4; j++) k = $urandom;\n"
      "      end\n"
      "    join\n"
      "    kept = p.get_randstate() == t2;\n"
      "    $display(\"%0d %0d %0d\", replayed, continued, kept);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 4 1\n");
}

}  // namespace
