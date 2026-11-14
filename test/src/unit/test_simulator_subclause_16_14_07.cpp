#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_placed_assertion_runs.h"

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

std::string Verdicts(const std::string& name) {
  return "    $display(\"" + name + " passed at %0d\", $time);\n" +
         "  else $display(\"" + name + " failed at %0d\", $time);\n";
}

std::string FlowSource(const std::string& clocking, const std::string& items) {
  return "module t;\n"
         "  logic clk1 = 0, clk2 = 0, a = 1, b = 1, rst = 0;\n"
         "  always #5 clk1 = ~clk1;\n"
         "  always #7 clk2 = ~clk2;\n"
         "  default clocking @(" +
         clocking +
         "); endclocking\n"
         "  property inner(e = $inferred_clock); @(e) b; endproperty\n"
         "  sequence sinner(e = $inferred_clock); @(e) b; endsequence\n" +
         items +
         "  initial begin #15 rst = 1; #5 b = 0; #3 b = 1; #2 rst = 0; end\n"
         "  initial #60 $finish;\n"
         "endmodule\n";
}

void ExpectFlowVerdicts(const std::string& src,
                        const std::vector<std::string>& want) {
  SCOPED_TRACE(src);
  SimFixture f;
  std::string out = RunCapture(src, f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
  EXPECT_EQ(PlacedSortedVerdicts(out), PlacedSorted(want));
}

std::vector<std::string> Clk2Verdicts() {
  return {"x passed at 7", "x failed at 21", "x passed at 35",
          "x passed at 49"};
}

std::vector<std::string> Clk2NextVerdicts() {
  return {"x failed at 21", "x passed at 35", "x passed at 49"};
}

void ExpectNestedVerdicts(const std::string& property,
                          const std::vector<std::string>& want) {
  ExpectFlowVerdicts(
      FlowSource("negedge clk1",
                 "  x: assert property (" + property + ")\n" + Verdicts("x")),
      want);
}

TEST(InferredClockingFunctionsRun,
     AContainersOwnDefaultClockingStandsInForTheDefault) {
  for (std::string kind : {"interface", "program", "checker"}) {
    std::string src = kind == "checker"
                          ? "checker w(clk1, clk2, b);\n"
                          : kind + " w(input logic clk1, clk2, b);\n";
    src.append(
        "  default clocking @(posedge clk2); endclocking\n"
        "  property inner(e = $inferred_clock); @(e) b; endproperty\n"
        "  x: assert property (inner)\n");
    src.append(Verdicts("x")).append("end").append(kind).append("\n");
    src.append(FlowSource("negedge clk1", "  w u(clk1, clk2, b);\n"));
    ExpectFlowVerdicts(src, Clk2Verdicts());
  }
}

TEST(InferredClockingFunctionsRun,
     AnImportedPropertyTakesTheInstantiatingModulesDefaults) {
  ExpectFlowVerdicts(
      "package pk;\n"
      "  property pp(x, e = $inferred_clock, d = $inferred_disable);\n"
      "    @(e) disable iff (d) x;\n"
      "  endproperty\n"
      "endpackage\n" +
          FlowSource("posedge clk2",
                     "  import pk::*;\n"
                     "  default disable iff rst;\n"
                     "  x: assert property (pp(b))\n" +
                         Verdicts("x")),
      {"x passed at 7", "x passed at 35", "x passed at 49"});
}

TEST(InferredClockingFunctionsRun,
     AnAssumeOrRestrictTakesTheDefaultsAtTheStatement) {
  ExpectFlowVerdicts(
      FlowSource("posedge clk2", "  x: assume property (inner)\n" +
                                     Verdicts("x") +
                                     "  restrict property (sinner);\n"),
      Clk2Verdicts());
}

TEST(
    InferredClockingFunctionsRun,
    DISABLED_APropertyInstanceAfterAnOverlappingImplicationTakesTheFlowingClock) {
  ExpectNestedVerdicts("@(posedge clk2) a |-> inner", Clk2Verdicts());
}

TEST(
    InferredClockingFunctionsRun,
    DISABLED_APropertyInstanceAfterANonOverlappingImplicationTakesTheFlowingClock) {
  ExpectNestedVerdicts("@(posedge clk2) a |=> inner", Clk2NextVerdicts());
}

TEST(InferredClockingFunctionsRun,
     DISABLED_ASequenceInstanceAfterAnImplicationTakesTheFlowingClock) {
  ExpectNestedVerdicts("@(posedge clk2) a |-> sinner", Clk2Verdicts());
}

TEST(InferredClockingFunctionsRun,
     ASequenceInstanceAfterACycleDelayTakesTheFlowingClock) {
  ExpectNestedVerdicts("@(posedge clk2) a ##1 sinner", Clk2NextVerdicts());
}

TEST(InferredClockingFunctionsRun,
     ANestedInstanceWhoseBodyWritesNoClockTakesTheFlowingClock) {
  ExpectFlowVerdicts(
      FlowSource("negedge clk1",
                 "  property inner3(e = $inferred_clock); b; endproperty\n"
                 "  x: assert property (@(posedge clk2) a |-> inner3)\n" +
                     Verdicts("x")),
      Clk2Verdicts());
}

TEST(InferredClockingFunctionsRun,
     DISABLED_ANestedInstancesInferredDisableIsTheDefaultAtTheInstance) {
  ExpectFlowVerdicts(
      FlowSource("negedge clk1",
                 "  default disable iff rst;\n"
                 "  sequence sdis(r = $inferred_disable); b || r; endsequence\n"
                 "  x: assert property (@(posedge clk2) disable iff (1'b0)\n"
                 "    a ##1 sdis)\n" +
                     Verdicts("x")),
      {"x passed at 21", "x passed at 35", "x passed at 49"});
}

TEST(InferredClockingFunctionsRun,
     DISABLED_APropertyInstanceUnderNotTakesTheFlowingClock) {
  ExpectFlowVerdicts(
      FlowSource("negedge clk1",
                 "  property innerneg(e = $inferred_clock); @(e) !b; "
                 "endproperty\n"
                 "  x: assert property (@(posedge clk2) not innerneg)\n" +
                     Verdicts("x")),
      Clk2Verdicts());
}

TEST(InferredClockingFunctionsRun,
     DISABLED_APropertyInstanceUnderAndOrOrTakesTheFlowingClock) {
  for (const char* property :
       {"@(posedge clk2) (a and inner)", "@(posedge clk2) (1'b0 or inner)"}) {
    ExpectNestedVerdicts(property, Clk2Verdicts());
  }
}

TEST(InferredClockingFunctionsRun,
     DISABLED_AnOuterPropertyAssertedInANestedModuleTakesItsClock) {
  ExpectFlowVerdicts(
      FlowSource("negedge clk1",
                 "  module n;\n"
                 "    default clocking @(posedge clk2); endclocking\n"
                 "    x: assert property (inner)\n" +
                     Verdicts("x") +
                     "  endmodule\n"
                     "  n u();\n"),
      Clk2Verdicts());
}

TEST(InferredClockingFunctionsRun,
     DISABLED_AMulticlockedBodysLeftOutClockTakesTheDefaultClocking) {
  ExpectFlowVerdicts(
      FlowSource(
          "negedge clk1",
          "  property p_multiclock(clkw, clkx = $inferred_clock, clky,\n"
          "                        w, x, y, z);\n"
          "    @clkw w ##1 @clkx x |=> @clky y ##1 z;\n"
          "  endproperty\n"
          "  x: assert property (p_multiclock(negedge clk2, , posedge clk1,\n"
          "                                   a, b, a, b))\n" +
              Verdicts("x")),
      {"x passed at 35", "x passed at 45"});
}

}  // namespace
