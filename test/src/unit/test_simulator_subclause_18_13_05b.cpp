#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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
      "        automatic process q = process::self();\n"
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

TEST(SetRandstateRun, AThisQualifiedCallRestoresTheObjectsState) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class P;\n"
      "    rand bit [15:0] v;\n"
      "    function string got_this(); return this.get_randstate(); "
      "endfunction\n"
      "    function string got_bare(); return get_randstate(); endfunction\n"
      "    function void put_this(string s); this.set_randstate(s); "
      "endfunction\n"
      "    function void put_bare(string s); set_randstate(s); endfunction\n"
      "  endclass\n"
      "  initial begin\n"
      "    static P o = new;\n"
      "    string s;\n"
      "    bit [15:0] first;\n"
      "    static int same = 0;\n"
      "    o.srandom(5);\n"
      "    repeat (8) begin\n"
      "      s = o.get_randstate();\n"
      "      void'(o.randomize());\n"
      "      first = o.v;\n"
      "      void'(o.randomize());\n"
      "      o.put_this(s);\n"
      "      void'(o.randomize());\n"
      "      if (o.v == first) same++;\n"
      "    end\n"
      "    $display(\"%0d\", same);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "8\n");
}

TEST(SetRandstateRun, DISABLED_AnUnqualifiedCallRestoresTheObjectsState) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class P;\n"
      "    rand bit [15:0] v;\n"
      "    function string got_this(); return this.get_randstate(); "
      "endfunction\n"
      "    function string got_bare(); return get_randstate(); endfunction\n"
      "    function void put_this(string s); this.set_randstate(s); "
      "endfunction\n"
      "    function void put_bare(string s); set_randstate(s); endfunction\n"
      "  endclass\n"
      "  initial begin\n"
      "    static P o = new;\n"
      "    string s;\n"
      "    bit [15:0] first;\n"
      "    static int same = 0;\n"
      "    o.srandom(5);\n"
      "    repeat (8) begin\n"
      "      s = o.get_randstate();\n"
      "      void'(o.randomize());\n"
      "      first = o.v;\n"
      "      void'(o.randomize());\n"
      "      o.put_bare(s);\n"
      "      void'(o.randomize());\n"
      "      if (o.v == first) same++;\n"
      "    end\n"
      "    $display(\"%0d\", same);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "8\n");
}

}  // namespace
