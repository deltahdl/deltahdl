#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(EventControlSim, AnUnpackedArrayElementWakesItsEventControl) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  logic c[2];\n"
                       "  int k = 0, w = 0, j = 1;\n"
                       "  always @(posedge c[0]) k++;\n"
                       "  always @(c[j]) w++;\n"
                       "  initial begin\n"
                       "    c[0] = 0; c[1] = 0;\n"
                       "    forever #5 begin c[0] = ~c[0]; c[1] = ~c[1]; end\n"
                       "  end\n"
                       "  initial #41 $display(\"%0d %0d\", k, w);\n"
                       "  initial #45 $finish;\n"
                       "endmodule\n",
                       f),
            "4 9\n$finish at time 45\n");
}

TEST(EventControlSim, AnArrayPortElementWakesTheInstancesEventControl) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module p(input logic c[2]);\n"
                       "  int k = 0;\n"
                       "  always @(posedge c[0]) k++;\n"
                       "  initial #41 $display(\"k=%0d\", k);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  logic cs[2] = '{0, 0};\n"
                       "  always #5 cs[0] = ~cs[0];\n"
                       "  p u(cs);\n"
                       "  initial #45 $finish;\n"
                       "endmodule\n",
                       f),
            "k=4\n$finish at time 45\n");
}

TEST(EventControlSim, AUserMethodResumesOnTheMemberItReads) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("class P;\n"
                 "  int status;\n"
                 "  int other;\n"
                 "  function int get_status(); return status; endfunction\n"
                 "endclass\n"
                 "module t;\n"
                 "  P p = new;\n"
                 "  initial begin\n"
                 "    @(p.get_status());\n"
                 "    $display(\"woke %0t %0d\", $time, p.status);\n"
                 "  end\n"
                 "  initial begin\n"
                 "    #2 p.other = 5;\n"
                 "    #3 p.status = 7;\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "woke 5 7\n");
}

TEST(EventControlSim,
     DISABLED_AFunctionOfADynamicArrayResumesOnResizeAndElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int d[];\n"
                       "  function int count(int x[]); return x.size(); "
                       "endfunction\n"
                       "  function int first(int x[]);\n"
                       "    return x.size() > 0 ? x[0] : -1;\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    @(count(d));\n"
                       "    $display(\"size %0t %0d\", $time, d.size());\n"
                       "    @(first(d));\n"
                       "    $display(\"elem %0t %0d\", $time, d[0]);\n"
                       "  end\n"
                       "  initial begin\n"
                       "    #2 d = new[3];\n"
                       "    #3 d[0] = 9;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "size 2 3\nelem 5 9\n");
}

TEST(EventControlSim, AWaitOnAMethodSummingMembersIsReleasedAtTheSum) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class H;\n"
                       "  int a, b;\n"
                       "  function int sum(); return a + b; endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  H h = new;\n"
                       "  initial begin\n"
                       "    wait (h.sum() == 20);\n"
                       "    $display(\"%0t\", $time);\n"
                       "  end\n"
                       "  initial begin\n"
                       "    #1 h.a = 10;\n"
                       "    #1 h.b = 10;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "2\n");
}

TEST(EventControlSim, AWaitOnASystemFunctionOfAQueueIsReleasedByPushes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  byte stream[$];\n"
                       "  initial begin\n"
                       "    wait ($bits(stream) > 60);\n"
                       "    $display(\"w %0t %0d\", $time, stream.size());\n"
                       "  end\n"
                       "  initial repeat (8) #1 stream.push_back(8'h1);\n"
                       "endmodule\n",
                       f),
            "w 8 8\n");
}

TEST(EventControlSim, DISABLED_AnEventOnASystemFunctionOfAQueueResumesOnAPush) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  byte stream[$];\n"
                       "  initial begin\n"
                       "    @($bits(stream));\n"
                       "    $display(\"e %0t\", $time);\n"
                       "  end\n"
                       "  initial repeat (8) #1 stream.push_back(8'h1);\n"
                       "endmodule\n",
                       f),
            "e 1\n");
}

TEST(EventControlSim, DISABLED_AMemberOfAReassignedHandleFollowsTheNewObject) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("class Packet;\n"
                 "  int status;\n"
                 "endclass\n"
                 "module t;\n"
                 "  Packet p = new;\n"
                 "  Packet q = new;\n"
                 "  Packet old;\n"
                 "  initial begin\n"
                 "    old = p;\n"
                 "    fork\n"
                 "      begin @(p.status); $display(\"s %0t\", $time); end\n"
                 "      begin @p; $display(\"h %0t\", $time); end\n"
                 "      #10 p = q;\n"
                 "    join\n"
                 "  end\n"
                 "  initial begin\n"
                 "    #15 old.status = 3;\n"
                 "    #5 q.status = 4;\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "h 10\ns 20\n");
}

TEST(EventControlSim,
     DISABLED_AMemberAlreadyDifferentInTheNewObjectResumesAtOnce) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("class Packet;\n"
                 "  int status;\n"
                 "endclass\n"
                 "module t;\n"
                 "  Packet p = new;\n"
                 "  Packet q = new;\n"
                 "  initial begin\n"
                 "    q.status = 5;\n"
                 "    fork\n"
                 "      begin @(p.status); $display(\"s %0t\", $time); end\n"
                 "      #10 p = q;\n"
                 "    join\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "s 10\n");
}

TEST(EventControlSim, AClockingInputEventFollowsTheSampledValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic clk = 0;\n"
                       "  logic d = 0;\n"
                       "  clocking cb @(posedge clk);\n"
                       "    input d;\n"
                       "  endclocking\n"
                       "  initial repeat (4) #5 clk = ~clk;\n"
                       "  initial #2 d = 1;\n"
                       "  initial begin\n"
                       "    @(cb.d);\n"
                       "    $display(\"%0t\", $time);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "5\n");
}

}  // namespace
