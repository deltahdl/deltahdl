#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_property_places.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

std::string SequenceMethodSource(const std::string& destination) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic sysclk = 0;\n"
         "  logic a = 0, b = 0, c = 0;\n"
         "  logic reset = 0, inst = 0, branch_back = 0;\n"
         "  logic reset1 = 0, branch_back1 = 0;\n"
         "  int ends = 0;\n"
         "  int last_end = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #8 sysclk = ~sysclk;\n"
         "  sequence e1;\n"
         "    @(posedge sysclk) $rose(a) ##1 b ##1 c;\n"
         "  endsequence\n"
         "  sequence e2_with_arg(sequence subseq);\n"
         "    @(posedge sysclk) reset ##1 inst ##1 subseq.triggered ##1 "
         "branch_back;\n"
         "  endsequence\n"
         "  sequence dest;\n" +
         destination +
         "  endsequence\n"
         "  initial forever begin\n"
         "    wait (dest.triggered);\n"
         "    ends++;\n"
         "    last_end = $time;\n"
         "    #1;\n"
         "  end\n"
         "  initial begin\n"
         "    #10 a = 1;\n"
         "    #10 reset = 1;\n"
         "    #10 reset = 0; b = 1;\n"
         "    #5 inst = 1;\n"
         "    #10 inst = 0;\n"
         "    #5 b = 0; c = 1; reset1 = 1;\n"
         "    #10 reset1 = 0;\n"
         "    #5 c = 0; branch_back = 1;\n"
         "    #5 branch_back1 = 1;\n"
         "    #5 branch_back = 0;\n"
         "    #5 branch_back1 = 0;\n"
         "    #10 $finish;\n"
         "  end\n"
         "endmodule\n";
}

struct EndPoints {
  uint64_t ends;
  uint64_t last_end;
};

EndPoints EndPointsOf(const std::string& destination) {
  SimFixture f;
  auto* ends = RunAndFindVar(SequenceMethodSource(destination), f, "ends");
  if (ends == nullptr) return {~0ull, ~0ull};
  Variable* last_end = f.ctx.FindVariable("last_end");
  return {ends->value.ToUint64(), last_end->value.ToUint64()};
}

TEST(SequenceMethods, TriggeredOnANamedSequenceReadsItsEndPoint) {
  EndPoints e2 = EndPointsOf(
      "    @(posedge sysclk) reset ##1 inst ##1 e1.triggered ##1 "
      "branch_back;\n");
  EXPECT_EQ(e2.ends, 1u);
  EXPECT_EQ(e2.last_end, 72u);
}

TEST(SequenceMethods, MatchedOnANamedSequenceStoresItsEndPointForAnotherClock) {
  EndPoints e3 = EndPointsOf(
      "    @(posedge clk) reset1 ##1 e1.matched ##1 branch_back1;\n");
  EXPECT_EQ(e3.ends, 1u);
  EXPECT_EQ(e3.last_end, 75u);
}

TEST(SequenceMethods, TriggeredOnASequenceFormalReadsTheActualsEndPoint) {
  EndPoints e4 =
      EndPointsOf("    e2_with_arg(@(posedge sysclk) $rose(a) ##1 b ##1 c);\n");
  EXPECT_EQ(e4.ends, 1u);
  EXPECT_EQ(e4.last_end, 72u);
}

TEST(SequenceMethods, AnActualThatNeverMatchesLeavesTheFormalsTriggeredFalse) {
  EndPoints e4 = EndPointsOf(
      "    e2_with_arg(@(posedge sysclk) $rose(reset1) ##1 b ##1 c);\n");
  EXPECT_EQ(e4.ends, 0u);
}

TEST(SequenceMethods, TriggeredInAnInstanceReadsItsOwnEndPoint) {
  SimFixture f;
  auto* u_hits = RunAndFindVar(
      "module child(input logic a, input logic clk);\n"
      "  int hits = 0;\n"
      "  sequence s; @(posedge clk) a ##1 a; endsequence\n"
      "  initial forever begin\n"
      "    wait (s.triggered);\n"
      "    hits = hits + 1;\n"
      "    @(posedge clk);\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0, a = 0, never = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  child u(a, clk);\n"
      "  child w(never, clk);\n"
      "  initial begin #2 a = 1; #30 a = 0; #20 $finish; end\n"
      "endmodule\n",
      f, "u.hits");
  ASSERT_NE(u_hits, nullptr);
  EXPECT_EQ(u_hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("w.hits")->value.ToUint64(), 0u);
}

TEST(SequenceMethods, TriggeredThroughAHierarchicalNameReadsThatInstances) {
  SimFixture f;
  auto* u_hits = RunAndFindVar(
      "module m(input logic clk, input logic v1);\n"
      "  logic v2 = 1;\n"
      "  sequence s; @(posedge clk) v1 ##1 v2; endsequence\n"
      "endmodule\n"
      "module t;\n"
      "  logic clk = 0, a = 0, never = 0;\n"
      "  int u_hits = 0, w_hits = 0, last = 0;\n"
      "  m u(clk, a);\n"
      "  m w(clk, never);\n"
      "  initial forever begin\n"
      "    wait (u.s.triggered);\n"
      "    u_hits++;\n"
      "    last = $time;\n"
      "    #1;\n"
      "  end\n"
      "  initial forever begin\n"
      "    wait (w.s.triggered);\n"
      "    w_hits++;\n"
      "    #1;\n"
      "  end\n"
      "  always #5 clk = ~clk;\n"
      "  initial begin #2 a = 1; #20 a = 0; #30 $finish; end\n"
      "endmodule\n",
      f, "u_hits");
  ASSERT_NE(u_hits, nullptr);
  EXPECT_EQ(u_hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 25u);
  EXPECT_EQ(f.ctx.FindVariable("w_hits")->value.ToUint64(), 0u);
}

TEST(SequenceMethods, TriggeredIsSetInTheObservedRegion) {
  SimFixture f;
  auto* active_hits = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0, v1 = 0, v2 = 1;\n"
      "  int active_hits = 0, waited_hits = 0;\n"
      "  sequence s; @(posedge clk) v1 ##1 v2; endsequence\n"
      "  always @(posedge clk) if (s.triggered) active_hits++;\n"
      "  initial forever begin\n"
      "    wait (s.triggered);\n"
      "    waited_hits++;\n"
      "    @(posedge clk);\n"
      "  end\n"
      "  always #5 clk = ~clk;\n"
      "  initial begin #2 v1 = 1; #20 v1 = 0; #30 $finish; end\n"
      "endmodule\n",
      f, "active_hits");
  ASSERT_NE(active_hits, nullptr);
  EXPECT_EQ(active_hits->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("waited_hits")->value.ToUint64(), 2u);
}

TEST(SequenceMethods, AClocklessSequenceReadOutsideAnAssertionTakesTheDefault) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  bit clk, a = 1, b = 1;\n"
      "  always #5 clk = ~clk;\n"
      "  clocking other @(negedge clk); endclocking\n"
      "  default clocking cb @(posedge clk); endclocking\n"
      "  sequence e4;\n"
      "    a ##1 b;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    wait (e4.triggered);\n"
      "    $display(\"e4 at %0t\", $time);\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("e4 at 15\n"), std::string::npos);
}

TEST(SequenceMethods, AClocklessSequenceReadInAProcedureTakesItsClock) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  bit clk, a = 1, b = 1;\n"
      "  int n = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  sequence e4;\n"
      "    a ##1 b;\n"
      "  endsequence\n"
      "  always @(posedge clk) if (e4.triggered) n++;\n"
      "  initial begin\n"
      "    wait (e4.triggered);\n"
      "    $display(\"e4 at %0t\", $time);\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("e4 at 15\n"), std::string::npos) << out;
}

std::string OperandRunSource(const std::string& items) {
  return "module t;\n"
         "  logic clk0 = 0, clk1 = 0, a;\n"
         "  always #5 clk0 = ~clk0;\n"
         "  always #4 clk1 = ~clk1;\n"
         "  initial begin a = 1; #20 a = 0; #10 a = 1; end\n"
         "  sequence s0; @(posedge clk0) a ##1 a; endsequence\n"
         "  sequence sa(x); @(posedge clk0) x ##1 x; endsequence\n" +
         items +
         "  initial #58 $finish;\n"
         "endmodule\n";
}

struct OperandRun {
  const char* items;
  PlaceCounts counts;
};

const OperandRun kAllowedOperandRuns[] = {
    {"  sequence dm(sequence q); @(posedge clk1) q.matched; endsequence\n"
     "  c1: cover sequence (dm(s0)) $display(\"PASS\");\n",
     {2, 0}},
    {"  property pt(sequence q); @(posedge clk0) q.triggered; endproperty\n"
     "  a1: assert property (pt(s0)) $display(\"PASS\"); "
     "else $display(\"FAIL\");\n",
     {3, 3}},
    {"  property pm(sequence q); @(posedge clk1) q.matched; endproperty\n"
     "  a1: assert property (pm(s0)) $display(\"PASS\"); "
     "else $display(\"FAIL\");\n",
     {2, 5}},
    {"  sequence ut(q); @(posedge clk0) q.triggered; endsequence\n"
     "  c1: cover sequence (ut(s0)) $display(\"PASS\");\n",
     {3, 0}},
    {"  sequence um(q); @(posedge clk1) q.matched; endsequence\n"
     "  c1: cover sequence (um(s0)) $display(\"PASS\");\n",
     {2, 0}},
    {"  property pu(q); @(posedge clk0) q.triggered; endproperty\n"
     "  a1: assert property (pu(s0)) $display(\"PASS\"); "
     "else $display(\"FAIL\");\n",
     {3, 3}}};

const OperandRun kUnreadOperandRuns[] = {
    {"  initial forever begin\n"
     "    wait (sa(a).triggered);\n"
     "    if (sa(a).triggered) $display(\"PASS\");\n"
     "    @(posedge clk0);\n"
     "  end\n",
     {3, 0}},
    {"  checker ck(q, logic c);\n"
     "    a1: assert property (@(posedge c) q.triggered) $display(\"PASS\"); "
     "else $display(\"FAIL\");\n"
     "  endchecker\n"
     "  ck k(s0, clk0);\n",
     {3, 3}}};

template <typename Runs>
void ExpectOperandRunsCount(const Runs& runs) {
  for (const OperandRun& run : runs) {
    SCOPED_TRACE(run.items);
    EXPECT_EQ(CountThroughTheEnd(OperandRunSource(run.items)), run.counts);
  }
}

TEST(SequenceMethodOperandRun, EachFormalOperandReadsTheEndPointOfItsActual) {
  ExpectOperandRunsCount(kAllowedOperandRuns);
}

TEST(SequenceMethodOperandRun,
     DISABLED_AnInstanceWithArgumentsInAWaitAndACheckersUntypedFormalAreRead) {
  ExpectOperandRunsCount(kUnreadOperandRuns);
}

TEST(SequenceMethodResult, TriggeredIsOneBitThatLastsTheRestOfItsTimeStep) {
  SimFixture f;
  std::string out =
      RunCapture(OperandRunSource(
                     "  int whole;\n"
                     "  sequence sw; @(posedge clk0) a ##[0:1] a; endsequence\n"
                     "  initial forever begin\n"
                     "    wait (sw.triggered);\n"
                     "    whole = sw.triggered;\n"
                     "    if ($bits(sw.triggered) == 1 && whole == 1) "
                     "$display(\"PASS\");\n"
                     "    #0 if (sw.triggered) $display(\"PASS\");\n"
                     "    #1 if (sw.triggered) $display(\"FAIL\");\n"
                     "    @(posedge clk0);\n"
                     "  end\n"),
                 f);
  EXPECT_EQ(CountedLines(out, "PASS"), 10u) << out;
  EXPECT_EQ(CountedLines(out, "FAIL"), 0u) << out;
}

std::string ProgramCheckSource(const std::string& delay) {
  return "module t;\n"
         "  logic sysclk = 0;\n"
         "  logic a = 0, b = 0, c = 0, reset = 0, inst = 0, branch_back = 0;\n"
         "  always #8 sysclk = ~sysclk;\n"
         "  sequence e1;\n"
         "    @(posedge sysclk) $rose(a) ##1 b ##1 c;\n"
         "  endsequence\n"
         "  sequence e2;\n"
         "    @(posedge sysclk) reset ##1 inst ##1 e1.triggered ##1 "
         "branch_back;\n"
         "  endsequence\n"
         "  program check;\n"
         "    initial begin\n" +
         delay +
         "      wait (e1.triggered || e2.triggered);\n"
         "      if (e1.triggered)\n"
         "        $display(\"e1 passed %0t\", $time);\n"
         "      if (e2.triggered)\n"
         "        $display(\"e2 passed %0t\", $time);\n"
         "      L2: $display(\"L2 %0t\", $time);\n"
         "    end\n"
         "  endprogram\n"
         "  initial begin\n"
         "    #10 a = 1;\n"
         "    #10 reset = 1;\n"
         "    #10 reset = 0; b = 1;\n"
         "    #5 inst = 1;\n"
         "    #10 inst = 0;\n"
         "    #5 b = 0; c = 1;\n"
         "    #15 c = 0; branch_back = 1;\n"
         "    #10 branch_back = 0;\n"
         "    #20 $finish;\n"
         "  end\n"
         "endmodule\n";
}

TEST(SequenceMethodExample, TheProgramResumesOnTheFirstEndAndNamesIt) {
  SimFixture f;
  std::string first = RunCapture(ProgramCheckSource(""), f);
  EXPECT_EQ(first, "e1 passed 56\nL2 56\n");
  SimFixture g;
  std::string later = RunCapture(ProgramCheckSource("      #60;\n"), g);
  EXPECT_EQ(later, "e2 passed 72\nL2 72\n");
}

}  // namespace
