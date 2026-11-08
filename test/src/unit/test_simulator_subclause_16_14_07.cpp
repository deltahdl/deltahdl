#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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

std::string RunInferredClockCase(const std::string& event) {
  SimFixture f;
  return RunCapture(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  logic en = 0; initial #42 en = 1;\n"
      "  logic a = 1;\n"
      "  int c1 = 0, c2 = 0;\n"
      "  default clocking @(" +
          event +
          "); endclocking\n"
          "  sequence s(untyped x, event e = $inferred_clock);\n"
          "    @(e) x;\n"
          "  endsequence\n"
          "  cover property (s(a)) c1++;\n"
          "  cover property (a) c2++;\n"
          "  initial #98 $display(\"c1=%0d c2=%0d\", c1, c2);\n"
          "endmodule\n",
      f);
}

TEST(InferredClockingFunctionsRun, AGuardedInferredClockKeepsItsGuard) {
  EXPECT_NE(RunInferredClockCase("posedge clk iff en").find("c1=6 c2=6\n"),
            std::string::npos);
}

TEST(InferredClockingFunctionsRun, AnOrJoinedInferredClockKeepsEachEvent) {
  EXPECT_NE(
      RunInferredClockCase("posedge clk or negedge clk").find("c1=19 c2=19\n"),
      std::string::npos);
}

TEST(InferredClockingFunctionsRun, AnEdgelessGuardedInferredClockStandsIn) {
  EXPECT_NE(RunInferredClockCase("clk iff en").find("c1=11 c2=11\n"),
            std::string::npos);
}

}  // namespace
