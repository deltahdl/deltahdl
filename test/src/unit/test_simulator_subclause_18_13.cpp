#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(RandomNumberFunctionsRun, TheSystemFunctionsReplayASeedAndStayInRange) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int unsigned a[4], b[4], r;\n"
      "  int i, replayed = 0, high = 0, in_range = 0;\n"
      "  initial begin\n"
      "    a[0] = $urandom(254);\n"
      "    for (i = 1; i < 4; i++) a[i] = $urandom;\n"
      "    b[0] = $urandom(254);\n"
      "    for (i = 1; i < 4; i++) b[i] = $urandom;\n"
      "    for (i = 0; i < 4; i++) if (a[i] == b[i]) replayed++;\n"
      "    for (i = 0; i < 32; i++) if ($urandom >= 32'h8000_0000) high = 1;\n"
      "    for (i = 0; i < 64; i++) begin\n"
      "      r = $urandom_range(7, 0); if (r <= 7) in_range++;\n"
      "      r = $urandom_range(7); if (r <= 7) in_range++;\n"
      "      r = $urandom_range(0, 7); if (r <= 7) in_range++;\n"
      "    end\n"
      "    $display(\"%0d %0d %0d\", replayed, high, in_range);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 1 192\n");
}

TEST(RandomNumberFunctionsRun, TheMethodsSeedAndRestoreAnObjectAndTheProcess) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class Packet;\n"
      "    rand bit [15:0] payload;\n"
      "  endclass\n"
      "  Packet pkt;\n"
      "  process p;\n"
      "  string st;\n"
      "  bit [15:0] pa[4], pb[4];\n"
      "  int unsigned a[4], b[4];\n"
      "  int i, k, obj_seed = 0, proc_seed = 0, obj_state = 0, proc_state = "
      "0;\n"
      "  initial begin\n"
      "    pkt = new;\n"
      "    p = process::self();\n"
      "    pkt.srandom(7);\n"
      "    for (i = 0; i < 4; i++) begin k = pkt.randomize(); pa[i] = "
      "pkt.payload; end\n"
      "    pkt.srandom(7);\n"
      "    for (i = 0; i < 4; i++) begin k = pkt.randomize(); pb[i] = "
      "pkt.payload; end\n"
      "    for (i = 0; i < 4; i++) if (pa[i] == pb[i]) obj_seed++;\n"
      "    p.srandom(55);\n"
      "    for (i = 0; i < 4; i++) a[i] = $urandom;\n"
      "    p.srandom(55);\n"
      "    for (i = 0; i < 4; i++) b[i] = $urandom;\n"
      "    for (i = 0; i < 4; i++) if (a[i] == b[i]) proc_seed++;\n"
      "    st = pkt.get_randstate();\n"
      "    for (i = 0; i < 4; i++) begin k = pkt.randomize(); pa[i] = "
      "pkt.payload; end\n"
      "    pkt.set_randstate(st);\n"
      "    for (i = 0; i < 4; i++) begin k = pkt.randomize(); pb[i] = "
      "pkt.payload; end\n"
      "    for (i = 0; i < 4; i++) if (pa[i] == pb[i]) obj_state++;\n"
      "    st = p.get_randstate();\n"
      "    for (i = 0; i < 4; i++) a[i] = $urandom;\n"
      "    p.set_randstate(st);\n"
      "    for (i = 0; i < 4; i++) b[i] = $urandom;\n"
      "    for (i = 0; i < 4; i++) if (a[i] == b[i]) proc_state++;\n"
      "    $display(\"%0d %0d %0d %0d\", obj_seed, proc_seed, obj_state, "
      "proc_state);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 4 4 4\n");
}

}  // namespace
