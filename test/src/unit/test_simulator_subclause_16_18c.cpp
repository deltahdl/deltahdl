#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

const char kPass[] = " $display(\"pass %0d\", $time); else;\n";
const char kSkewed[] =
    "  clocking c2 @(posedge clk); input #2 a, b, v; endclocking\n";
const char kBlockSample[] = "pass 35\npass 45\n$finish at time 70\n";
const char kPlainSample[] = "pass 25\npass 35\n$finish at time 70\n";

std::string Top(const std::string& body, const std::string& outside = "") {
  return outside +
         "module t;\n"
         "  logic clk = 0;\n"
         "  logic a = 0, b = 0;\n"
         "  logic [3:0] v = 4'd0;\n"
         "  always #5 clk = ~clk;\n"
         "  initial begin\n"
         "    #24 a = 1; v = 4'd5;\n"
         "    #10 b = 1;\n"
         "    #10 a = 0; v = 4'd9;\n"
         "    #10 b = 0;\n"
         "    #16 $finish;\n"
         "  end\n" +
         body + "endmodule\n";
}

std::string Simulate(const std::string& src) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  return out;
}

TEST(ClockingVariableAssertionRun, AnAssertReadsTheSkewedSampleNotTheSignal) {
  EXPECT_EQ(Simulate(Top(std::string(kSkewed) +
                         "  k: assert property (@(posedge clk) c2.a)" + kPass)),
            kBlockSample);
  EXPECT_EQ(Simulate(Top(std::string(kSkewed) +
                         "  k: assert property (@(posedge clk) a)" + kPass)),
            kPlainSample);
}

TEST(ClockingVariableAssertionRun, AnAssumeReadsTheBlocksSample) {
  EXPECT_EQ(Simulate(Top(std::string(kSkewed) +
                         "  k: assume property (@(posedge clk) c2.a)" + kPass)),
            kBlockSample);
}

TEST(ClockingVariableAssertionRun, ACoverPropertyReadsTheBlocksSample) {
  EXPECT_EQ(Simulate(Top(std::string(kSkewed) +
                         "  k: cover property (@(posedge clk) c2.a)"
                         " $display(\"pass %0d\", $time);\n")),
            kBlockSample);
}

TEST(ClockingVariableAssertionRun, ACoverSequenceReadsTheBlocksSample) {
  EXPECT_EQ(Simulate(Top(std::string(kSkewed) +
                         "  k: cover sequence (@(posedge clk) c2.a)"
                         " $display(\"pass %0d\", $time);\n")),
            kBlockSample);
}

TEST(ClockingVariableAssertionRun, ANamedSequenceReadsTheBlocksSample) {
  EXPECT_EQ(Simulate(Top(std::string(kSkewed) +
                         "  sequence s; @(posedge clk) c2.a; endsequence\n"
                         "  k: assert property (s)" +
                         kPass)),
            kBlockSample);
}

TEST(ClockingVariableAssertionRun, EachTickOfASequenceReadsTheBlocksSample) {
  EXPECT_EQ(Simulate(Top(std::string(kSkewed) +
                         "  k: assert property (@(posedge clk) c2.a ##1 c2.b)" +
                         kPass)),
            "pass 45\npass 55\n$finish at time 70\n");
  EXPECT_EQ(
      Simulate(Top(std::string(kSkewed) +
                   "  k: assert property (@(posedge clk) a ##1 b)" + kPass)),
      "pass 35\npass 45\n$finish at time 70\n");
}

TEST(ClockingVariableAssertionRun, SampledValueFunctionsReadTheBlocksSample) {
  struct Case {
    const char* expr;
    const char* expected;
  };
  const Case kCases[] = {
      {"$rose(c2.a)", "pass 35\n$finish at time 70\n"},
      {"$fell(c2.a)", "pass 55\n$finish at time 70\n"},
      {"$stable(c2.a) && c2.a", "pass 45\n$finish at time 70\n"},
      {"$changed(c2.a)", "pass 35\npass 55\n$finish at time 70\n"},
      {"$past(c2.a)", "pass 45\npass 55\n$finish at time 70\n"},
      {"$sampled(c2.a)", kBlockSample},
      {"$rose(a)", "pass 25\n$finish at time 70\n"},
  };
  for (const auto& c : kCases) {
    EXPECT_EQ(Simulate(Top(std::string(kSkewed) +
                           "  k: assert property (@(posedge clk) " + c.expr +
                           ")" + kPass)),
              c.expected)
        << c.expr;
  }
}

TEST(ClockingVariableAssertionRun, ANamedPropertysActualReadsTheBlocksSample) {
  EXPECT_EQ(Simulate(Top(std::string(kSkewed) +
                         "  property p(x); @(posedge clk) x; endproperty\n"
                         "  k: assert property (p(c2.a))" +
                         kPass)),
            kBlockSample);
}

TEST(ClockingVariableAssertionRun, ANamedSequencesActualReadsTheBlocksSample) {
  EXPECT_EQ(Simulate(Top(std::string(kSkewed) +
                         "  sequence s(x); x; endsequence\n"
                         "  k: assert property (@(posedge clk) s(c2.a))" +
                         kPass)),
            kBlockSample);
}

TEST(ClockingVariableAssertionRun, AProceduralAssertionReadsTheBlocksSample) {
  EXPECT_EQ(Simulate(Top(std::string(kSkewed) +
                         "  always @(posedge clk) begin\n"
                         "    k: assert property (c2.a)" +
                         kPass + "  end\n")),
            kBlockSample);
}

TEST(ClockingVariableAssertionRun, AZeroSkewSampleTakesTheValueSetAtTheEdge) {
  const std::string kDesign =
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic a = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  clocking c0 @(posedge clk); input #0 a; endclocking\n"
      "  initial begin\n"
      "    #25 a = 1;\n"
      "    #20 a = 0;\n"
      "    #25 $finish;\n"
      "  end\n";
  EXPECT_EQ(Simulate(kDesign + "  k: assert property (@(posedge clk) c0.a)" +
                     kPass + "endmodule\n"),
            "pass 25\npass 35\n$finish at time 70\n");
  EXPECT_EQ(Simulate(kDesign + "  k: assert property (@(posedge clk) a)" +
                     kPass + "endmodule\n"),
            "pass 35\npass 45\n$finish at time 70\n");
}

TEST(ClockingVariableAssertionRun, AnExplicitStepSkewMatchesThePlainSample) {
  EXPECT_EQ(Simulate(Top("  clocking c1 @(posedge clk); input #1step a; "
                         "endclocking\n"
                         "  k: assert property (@(posedge clk) c1.a)" +
                         std::string(kPass))),
            kPlainSample);
}

TEST(ClockingVariableAssertionRun,
     DISABLED_AnInoutClockingVariableReadsTheBlocksSample) {
  EXPECT_EQ(Simulate(Top("  clocking c2 @(posedge clk);\n"
                         "    default input #2 output #0;\n"
                         "    inout a;\n"
                         "  endclocking\n"
                         "  k: assert property (@(posedge clk) c2.a)" +
                         std::string(kPass))),
            kBlockSample);
}

TEST(ClockingVariableAssertionRun, AMultiBitClockingInputReadsTheBlocksSample) {
  EXPECT_EQ(Simulate(Top(std::string(kSkewed) +
                         "  k: assert property (@(posedge clk) c2.v == 4'd5)" +
                         kPass)),
            kBlockSample);
  EXPECT_EQ(Simulate(Top(std::string(kSkewed) +
                         "  k: assert property (@(posedge clk) c2.v == 4'd9)" +
                         kPass)),
            "pass 55\npass 65\n$finish at time 70\n");
  EXPECT_EQ(
      Simulate(Top(std::string(kSkewed) +
                   "  k: assert property (@(posedge clk) v == 4'd5)" + kPass)),
      kPlainSample);
}

const char kInterface[] =
    "interface ifc(input logic clk, input logic a);\n"
    "  clocking cb @(posedge clk); input #2 a; endclocking\n"
    "endinterface\n";

TEST(ClockingVariableAssertionRun, AnInterfacesOwnAssertionReadsItsBlock) {
  EXPECT_EQ(
      Simulate(Top("  ifc i(clk, a);\n",
                   "interface ifc(input logic clk, input logic a);\n"
                   "  clocking cb @(posedge clk); input #2 a; endclocking\n"
                   "  k: assert property (@(posedge clk) cb.a)" +
                       std::string(kPass) + "endinterface\n")),
      kBlockSample);
}

TEST(ClockingVariableAssertionRun, AnInterfacePortsBlockReadsItsSample) {
  EXPECT_EQ(Simulate(Top("  ifc i(clk, a);\n  m u(i);\n",
                         std::string(kInterface) +
                             "module m(ifc i);\n"
                             "  k: assert property (@(posedge i.clk) i.cb.a)" +
                             kPass + "endmodule\n")),
            kBlockSample);
}

TEST(ClockingVariableAssertionRun, AProgramsAssertionReadsItsBlock) {
  EXPECT_EQ(
      Simulate(Top("  p u(clk, a);\n",
                   "program p(input logic clk, input logic a);\n"
                   "  clocking cb @(posedge clk); input #2 a; endclocking\n"
                   "  k: assert property (@(posedge clk) cb.a)" +
                       std::string(kPass) + "endprogram\n")),
      kBlockSample);
}

TEST(ClockingVariableAssertionRun, ACheckersOwnBlockFeedsItsAssertion) {
  EXPECT_EQ(Simulate(Top("  chk k(a, clk);\n",
                         "checker chk(logic x, logic c);\n"
                         "  clocking cb @(posedge c); input #2 x; endclocking\n"
                         "  k: assert property (@(posedge c) cb.x)" +
                             std::string(kPass) + "endchecker\n")),
            kBlockSample);
}

TEST(ClockingVariableAssertionRun, AChildInstancesBlockReadByPath) {
  EXPECT_EQ(
      Simulate(Top("  child u(clk, a);\n"
                   "  k: assert property (@(posedge clk) u.cb.a)" +
                       std::string(kPass),
                   "module child(input logic clk, input logic a);\n"
                   "  clocking cb @(posedge clk); input #2 a; endclocking\n"
                   "endmodule\n")),
      kBlockSample);
}

TEST(ClockingVariableAssertionRun, AGenerateBlocksAssertionReadsItsBlock) {
  EXPECT_EQ(
      Simulate(Top("  if (1) begin : g\n"
                   "    clocking cb @(posedge clk); input #2 a; endclocking\n"
                   "    k: assert property (@(posedge clk) cb.a)" +
                   std::string(kPass) + "  end\n")),
      kBlockSample);
}

TEST(ClockingVariableAssertionRun,
     DISABLED_AGenerateBlocksClockingVariableReadFromOutside) {
  EXPECT_EQ(
      Simulate(Top("  if (1) begin : g\n"
                   "    clocking cb @(posedge clk); input #2 a; endclocking\n"
                   "  end\n"
                   "  k: assert property (@(posedge clk) g.cb.a)" +
                   std::string(kPass))),
      kBlockSample);
}

const char kDefaultSkewed[] =
    "  default clocking cb @(posedge clk); input #2 a; endclocking\n";

TEST(ClockingVariableAssertionRun, ADefaultBlocksVariableUnderAnExplicitClock) {
  EXPECT_EQ(Simulate(Top(std::string(kDefaultSkewed) +
                         "  k: assert property (@(posedge clk) cb.a)" + kPass)),
            kBlockSample);
}

TEST(ClockingVariableAssertionRun, ADefaultClockedExpressionReadsTheSample) {
  EXPECT_EQ(Simulate(Top(std::string(kDefaultSkewed) +
                         "  k: assert property (cb.a == 1'b1)" + kPass)),
            kBlockSample);
}

TEST(ClockingVariableAssertionRun,
     DISABLED_ADefaultClockedPropertyOfTheVariableAloneReadsTheSample) {
  EXPECT_EQ(Simulate(Top(std::string(kDefaultSkewed) +
                         "  k: assert property (cb.a)" + kPass)),
            kBlockSample);
}

}  // namespace
