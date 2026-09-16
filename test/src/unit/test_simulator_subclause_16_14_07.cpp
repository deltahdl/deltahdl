#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A module around the items given, as
// test/src/e2e/inferred_clocking_functions.sv is: clk1 rises at 5, 15, ...
// and falls at 10, 20, ..., clk2 rises at 13 and 33, the default clocking
// is negedge clk1 and the default disable iff is rst1, a and b are 1
// throughout, c is 1 from 12 to 28, rst1 from 36 to 42, and the run ends
// at 48; the clause's p_triggers defaults its clock and its disable
// condition to the inferred functions. The attempts still in flight at the
// end hold in the final processes, which the fixture's run does not reach
// and the e2e design shows.
std::string InferredSource(const std::string& items) {
  return "module t;\n"
         "  logic a = 1, b = 1, c = 0, rst1 = 0, clk1 = 0, clk2 = 0;\n"
         "  logic rst = 0;\n"
         "  int rst_seen = 0;\n"
         "  always #5 clk1 = ~clk1;\n"
         "  initial begin\n"
         "    #3;\n"
         "    forever #10 clk2 = ~clk2;\n"
         "  end\n"
         "  default clocking @(negedge clk1); endclocking\n"
         "  default disable iff rst1;\n"
         "  property p_triggers(start_event, end_event, form,\n"
         "                      clk = $inferred_clock,\n"
         "                      rst = $inferred_disable);\n"
         "    @clk disable iff (rst) (start_event ##0 end_event[->1]) |=> "
         "form;\n"
         "  endproperty\n" +
         items +
         "  initial begin\n"
         "    #12 c = 1;\n"
         "    #16 c = 0;\n"
         "    #8 rst1 = 1;\n"
         "    #6 rst1 = 0;\n"
         "    #6 $finish;\n"
         "  end\n"
         "endmodule\n";
}

// §16.14.7: in the clause's a1 the clock is inferred from the default
// clocking, negedge clk1, and the disable condition from the default
// disable iff, rst1, so a1 reports as the assertion it is logically
// equivalent to: passing at 20, failing at 30, its attempt of 30 dropped
// and its attempt of 40 disabled while rst1 is 1.
TEST(InferredClockingFunctionsRun,
     TheDefaultClockingAndDisableStandInForTheDefaults) {
  SimFixture f;
  std::string out = RunCapture(
      InferredSource(
          "  a1: assert property (p_triggers(a, b, c))\n"
          "    $display(\"a1 passed at %0d\", $time);\n"
          "  else $display(\"a1 failed at %0d\", $time);\n"
          "  a1_explicit: assert property (@(negedge clk1)\n"
          "    disable iff (rst1) (a ##0 b[->1]) |=> c)\n"
          "    $display(\"a1_explicit passed at %0d\", $time);\n"
          "  else $display(\"a1_explicit failed at %0d\", $time);\n"),
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out,
            "a1 passed at 20\na1_explicit passed at 20\n"
            "a1 failed at 30\na1_explicit failed at 30\n"
            "$finish at time 48\n");
}

// §16.14.7: in the clause's a2 the event expression posedge clk1 is passed
// to the formal clk and 1'b0 to rst, so neither inferred function is used
// and a2 reports as its equivalent on posedge clk1 disabled by nothing.
TEST(InferredClockingFunctionsRun, AnActualSuppliedStandsInsteadOfTheDefault) {
  SimFixture f;
  std::string out = RunCapture(
      InferredSource(
          "  a2: assert property (p_triggers(a, b, c, posedge clk1, 1'b0))\n"
          "    $display(\"a2 passed at %0d\", $time);\n"
          "  else $display(\"a2 failed at %0d\", $time);\n"
          "  a2_explicit: assert property (@(posedge clk1)\n"
          "    disable iff (1'b0) (a ##0 b[->1]) |=> c)\n"
          "    $display(\"a2_explicit passed at %0d\", $time);\n"
          "  else $display(\"a2_explicit failed at %0d\", $time);\n"),
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out,
            "a2 passed at 15\na2_explicit passed at 15\n"
            "a2 passed at 25\na2_explicit passed at 25\n"
            "a2 failed at 35\na2_explicit failed at 35\n"
            "a2 failed at 45\na2_explicit failed at 45\n"
            "$finish at time 48\n");
}

// §16.14.7: in the clause's a3 the clocking event is inferred from the
// event control of the always procedure, posedge clk2, reset being
// referenced within it, and the disable condition from the default disable
// iff, so a3 reports as its equivalent on posedge clk2, failing at 33.
TEST(InferredClockingFunctionsRun,
     TheProceduresInferredClockStandsInForTheDefault) {
  SimFixture f;
  std::string out = RunCapture(
      InferredSource(
          "  always @(posedge clk2 or posedge rst) begin\n"
          "    if (rst) rst_seen++;\n"
          "    else begin\n"
          "      a3: assert property (p_triggers(a, b, c))\n"
          "        $display(\"a3 passed at %0d\", $time);\n"
          "      else $display(\"a3 failed at %0d\", $time);\n"
          "      a3_explicit: assert property (@(posedge clk2)\n"
          "        disable iff (rst1) (a ##0 b[->1]) |=> c)\n"
          "        $display(\"a3_explicit passed at %0d\", $time);\n"
          "      else $display(\"a3_explicit failed at %0d\", $time);\n"
          "    end\n"
          "  end\n"),
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out,
            "a3 failed at 33\na3_explicit failed at 33\n"
            "$finish at time 48\n");
}

// §16.14.7: outside the scope of any default disable iff declaration,
// $inferred_disable returns 1'b0, so the instance is disabled by nothing
// and rst1 rising at 36 drops no attempt: the attempt of 30 fails at 40.
TEST(InferredClockingFunctionsRun, OutsideAnyDefaultDisableTheDefaultIsFalse) {
  SimFixture f;
  std::string src = InferredSource(
      "  a1: assert property (p_triggers(a, b, c))\n"
      "    $display(\"a1 passed at %0d\", $time);\n"
      "  else $display(\"a1 failed at %0d\", $time);\n");
  src.replace(src.find("  default disable iff rst1;\n"),
              std::string("  default disable iff rst1;\n").size(), "");
  std::string out = RunCapture(src, f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out,
            "a1 passed at 20\na1 failed at 30\na1 failed at 40\n"
            "$finish at time 48\n");
}

}  // namespace
