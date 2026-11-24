#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <sstream>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

struct Levels {
  std::string a;
  std::string b;
};

struct Pulse {
  int start;
  int length;
};

std::string Pattern(const std::string& levels) {
  std::string bits(levels.rbegin(), levels.rend());
  return "4'b" + bits;
}

std::string Design(const Levels& levels, const Pulse& pulse,
                   const std::string& checked) {
  return "module t;\n  bit clk = 0, c2 = 0, a, b, r = 0;\n  int n, passes = 0, "
         "fails = 0;\n"
         "  bit [3:0] pa = " +
         Pattern(levels.a) + ", pb = " + Pattern(levels.b) +
         ";\n"
         "  initial begin\n"
         "    for (int k = 0; k < 4; k++) begin\n"
         "      a = pa[k]; b = pb[k]; n = k;\n"
         "      #5 clk = 1;\n"
         "      #2 a = ~a; b = ~b; n = k + 100;\n"
         "      #1 c2 = 1;\n"
         "      #1 clk = 0; c2 = 0;\n"
         "      #1;\n"
         "    end\n"
         "    $finish;\n"
         "  end\n"
         "  initial begin #" +
         std::to_string(pulse.start) + " r = 1; #" +
         std::to_string(pulse.length) + " r = 0; end\n" + checked +
         "endmodule\n";
}

std::string Reported(const std::string& property) {
  return "  assert property (" + property +
         ") $display(\"p%0t\", $time); else $display(\"f%0t\", $time);\n";
}

std::string Counted(const std::string& property) {
  return "  assert property (" + property + ") passes++; else fails++;\n";
}

std::string Verdicts(const std::string& out) {
  std::istringstream lines(out);
  std::vector<std::string> verdicts;
  for (std::string line; std::getline(lines, line);) {
    if (!line.empty() && (line[0] == 'p' || line[0] == 'f')) {
      verdicts.push_back(line);
    }
  }
  std::sort(verdicts.begin(), verdicts.end(),
            [](const std::string& x, const std::string& y) {
              const int kX = std::stoi(x.substr(1));
              const int kY = std::stoi(y.substr(1));
              return kX != kY ? kX < kY : x < y;
            });
  std::string joined;
  for (const auto& verdict : verdicts) {
    if (!joined.empty()) joined += ' ';
    joined += verdict;
  }
  return joined;
}

void ExpectVerdicts(const std::string& src, const std::string& verdicts) {
  SimFixture f;
  EXPECT_EQ(Verdicts(RunCapture(src, f)), verdicts) << src;
}

constexpr Pulse kNoPulse = {1, 1};
constexpr Pulse kBetweenTicks = {22, 1};
constexpr Pulse kOverATick = {24, 2};
constexpr Pulse kOverTheOtherTick = {27, 2};

void ExpectPulsed(const Levels& levels, const Pulse& pulse,
                  const std::string& spec, const std::string& verdicts) {
  ExpectVerdicts(Design(levels, pulse, Reported(spec)), verdicts);
}

void ExpectSpec(const Levels& levels, const std::string& spec,
                const std::string& verdicts) {
  ExpectPulsed(levels, kNoPulse, "@(posedge clk) " + spec, verdicts);
}

void ExpectNamed(const Levels& levels, const Pulse& pulse,
                 const std::string& body, const std::string& verdicts) {
  ExpectVerdicts(Design(levels, pulse,
                        "  property q; " + body + "; endproperty\n" +
                            Reported("@(posedge clk) 1 |-> q")),
                 verdicts);
}

void ExpectLocal(const std::string& body, const std::string& verdicts) {
  ExpectVerdicts(Design({"0000", "0000"}, kNoPulse,
                        "  property q; int v; " + body + "; endproperty\n" +
                            Reported("q")),
                 verdicts);
}

void ExpectCounts(const Levels& levels, const Pulse& pulse,
                  const std::string& spec, std::uint64_t passes,
                  std::uint64_t fails) {
  SimFixture f;
  const std::string kSrc =
      Design(levels, pulse, Counted("@(posedge clk) " + spec));
  auto* counted = RunAndFindVar(kSrc, f, "passes");
  ASSERT_NE(counted, nullptr) << kSrc;
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(counted->value.ToUint64(), passes) << kSrc;
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), fails) << kSrc;
}

TEST(ClockRewriteAtARun, ABooleanIsSampledAtTheTickOfItsClock) {
  ExpectSpec({"1011", "0000"}, "a", "p5 f15 p25 p35");
}

TEST(ClockRewriteAtARun, ABooleanWaitsForTheNextTickOfItsClock) {
  ExpectSpec({"1011", "0000"}, "1 ##0 @(posedge c2) a", "f8 p18 f28 f38");
  ExpectSpec({"1011", "0000"}, "1 |-> @(posedge c2) a", "f8 p18 f28 f38");
}

TEST(ClockRewriteAtARun, AMatchItemTakesItsValueAtTheTick) {
  ExpectLocal("@(posedge clk) (1, v = n) ##1 (n == v + 1)", "p15 p25 p35");
  ExpectLocal("@(posedge clk) (1, v = n) ##1 (n == v + 101)", "f15 f25 f35");
}

TEST(ClockRewriteAtARun, AMatchItemTakesItsValueAtANestedClocksTick) {
  ExpectLocal("@(posedge clk) 1 ##0 @(posedge c2) (1, v = n) ##0 (v >= 100)",
              "p8 p18 p28 p38");
  ExpectLocal("@(posedge clk) (1, v = n) ##0 @(posedge c2) (n == v + 100)",
              "p8 p18 p28 p38");
}

TEST(ClockRewriteAtARun, ANestedClockReplacesTheClockOfASequence) {
  ExpectSpec({"1101", "0110"}, "a ##1 @(posedge c2) b", "p8 f18 f25 p38");
}

TEST(ClockRewriteAtARun, DISABLED_AnOuterClockIsReplacedWhollyByANestedOne) {
  ExpectSpec({"1011", "0000"}, "(@(posedge c2) a)", "f8 p18 f28 f38");
  ExpectSpec({"1011", "0000"}, "(@(posedge c2) not a)", "p8 f18 p28 p38");
}

TEST(ClockRewriteAtARun, ADelayOfOneMovesToTheNextTick) {
  ExpectSpec({"1100", "1010"}, "a ##1 b", "f15 f25 p25 f35");
}

TEST(ClockRewriteAtARun, ADelayOfZeroStaysAtTheTick) {
  ExpectSpec({"1101", "1010"}, "a ##0 b", "p5 f15 f25 f35");
  ExpectSpec({"1101", "1010"}, "a ##0 b ##1 a", "f15 p15 f25 f35");
}

TEST(ClockRewriteAtARun, EachOperandOfASequenceOrIsClocked) {
  ExpectSpec({"1101", "0101"}, "(a ##1 b) or b", "p15 p15 f25 p35");
}

TEST(ClockRewriteAtARun, EachOperandOfIntersectIsClocked) {
  ExpectSpec({"1110", "1101"}, "(a ##1 b) intersect (b ##1 a)",
             "p15 f25 f25 f35");
  ExpectSpec({"1110", "1101"}, "a[*1:2] intersect (1 ##1 b)",
             "p15 f25 f35 f35");
}

TEST(ClockRewriteAtARun, TheOperandOfFirstMatchIsClocked) {
  ExpectSpec({"0100", "0110"}, "first_match(1 ##[0:2] b) |-> a", "p15 p15 f25");
}

TEST(ClockRewriteAtARun, AnEmptyRepetitionTakesNoTick) {
  ExpectSpec({"0000", "1010"}, "a[*0] ##1 b", "p5 f15 p25 f35");
}

TEST(ClockRewriteAtARun, EachIterationOfARepetitionIsClocked) {
  ExpectSpec({"1100", "0010"}, "a[*1:$] ##1 b", "f25 p25 p25 f35");
  ExpectSpec({"0011", "1101"}, "1 ##0 @(posedge c2) (a[*1:$] ##1 b)",
             "f28 p28 p28 f38");
}

TEST(ClockRewriteAtARun, AStrongSequenceIsClocked) {
  ExpectCounts({"1101", "1010"}, kNoPulse, "strong(a ##1 b)", 1, 3);
}

TEST(ClockRewriteAtARun, AWeakSequenceIsClocked) {
  ExpectSpec({"1101", "1010"}, "weak(a ##1 b)", "f15 f25 p25");
  ExpectCounts({"1101", "1010"}, kNoPulse, "weak(a ##1 b)", 1, 2);
}

TEST(ClockRewriteAtARun, ANestedClockReplacesTheClockOfAProperty) {
  ExpectSpec({"1101", "0110"}, "a |-> @(posedge c2) b", "p8 f18 p25 p38");
}

TEST(ClockRewriteAtARun, DISABLED_ADisableConditionActsBetweenTicks) {
  ExpectCounts({"1110", "0000"}, kNoPulse, "disable iff (r) a ##1 b", 0, 4);
  ExpectCounts({"1110", "0000"}, kBetweenTicks, "disable iff (r) a ##1 b", 0,
               3);
}

TEST(ClockRewriteAtARun, AnAcceptConditionActsBetweenTicks) {
  ExpectCounts({"1110", "0000"}, kNoPulse, "accept_on (r) a ##1 b", 0, 4);
  ExpectCounts({"1110", "0000"}, kBetweenTicks, "accept_on (r) a ##1 b", 1, 3);
}

TEST(ClockRewriteAtARun, ARejectConditionActsBetweenTicks) {
  ExpectCounts({"1110", "1111"}, kNoPulse, "reject_on (r) a ##1 b", 3, 1);
  ExpectCounts({"1110", "1111"}, kBetweenTicks, "reject_on (r) a ##1 b", 2, 2);
}

TEST(ClockRewriteAtARun, ASynchronousAcceptActsAtATickOnly) {
  ExpectPulsed({"1111", "0000"}, kBetweenTicks,
               "@(posedge clk) sync_accept_on (r) a ##1 b", "f15 f25 f35");
  ExpectPulsed({"1111", "0000"}, kOverATick,
               "@(posedge clk) sync_accept_on (r) a ##1 b", "f15 p25 p25");
}

TEST(ClockRewriteAtARun, ASynchronousRejectActsAtATickOnly) {
  ExpectPulsed({"1111", "1111"}, kBetweenTicks,
               "@(posedge clk) sync_reject_on (r) a ##1 b", "p15 p25 p35");
  ExpectPulsed({"1111", "1111"}, kOverATick,
               "@(posedge clk) sync_reject_on (r) a ##1 b", "p15 f25 f25");
}

TEST(ClockRewriteAtARun, DISABLED_ASynchronousAcceptTicksOnTheIncomingClock) {
  const std::string kSpec =
      "@(posedge clk) 1 |-> sync_accept_on (r) (@(posedge c2) a)";
  ExpectPulsed({"1111", "0000"}, kOverATick, kSpec, "f8 f18 p25 f38");
  ExpectPulsed({"1111", "0000"}, kOverTheOtherTick, kSpec, "f8 f18 f28 f38");
}

TEST(ClockRewriteAtARun, DISABLED_ASynchronousRejectTicksOnTheIncomingClock) {
  const std::string kSpec =
      "@(posedge clk) 1 |-> sync_reject_on (r) (@(posedge c2) a)";
  ExpectPulsed({"0000", "0000"}, kOverATick, kSpec, "p8 p18 f25 p38");
  ExpectPulsed({"0000", "0000"}, kOverTheOtherTick, kSpec, "p8 p18 p28 p38");
}

TEST(ClockRewriteAtARun, TheOperandOfNotIsClocked) {
  ExpectSpec({"1100", "1010"}, "not (a ##1 b)", "p15 f25 p25 p35");
  ExpectSpec({"1011", "0000"}, "1 |-> not (@(posedge c2) a)", "p8 f18 p28 p38");
}

TEST(ClockRewriteAtARun, DISABLED_TheOperandOfANamedPropertysNotIsClocked) {
  ExpectNamed({"1011", "0000"}, kNoPulse, "not (@(posedge c2) a)",
              "p8 f18 p28 p38");
}

TEST(ClockRewriteAtARun, BothSidesOfAnImplicationAreClocked) {
  ExpectSpec({"1101", "1001"}, "a |-> b", "p5 f15 p25 p35");
  ExpectSpec({"1100", "0110"}, "a ##1 b |-> a", "p15 f25 p25 p35");
}

TEST(ClockRewriteAtARun, EachOperandOfAPropertyOrIsClocked) {
  ExpectSpec({"1001", "0100"},
             "1 |-> ((@(posedge clk) a) or (@(posedge c2) b))",
             "p5 f18 p28 p35");
}

TEST(ClockRewriteAtARun, EachOperandOfAPropertyAndIsClocked) {
  ExpectSpec({"1110", "0100"},
             "1 |-> ((@(posedge clk) a) and (@(posedge c2) b))",
             "p8 f18 p28 f35");
}

TEST(ClockRewriteAtARun, NexttimeLooksAtTheNextTick) {
  ExpectSpec({"0110", "0000"}, "nexttime a", "p15 p25 f35");
}

TEST(ClockRewriteAtARun, NexttimeLooksPastTheFirstTickOfItsOwnClock) {
  ExpectSpec({"0110", "0000"}, "1 |-> @(posedge c2) nexttime a", "f18 f28 p38");
}

TEST(ClockRewriteAtARun, BothOperandsOfUntilAreReadAtTicks) {
  ExpectSpec({"1100", "0010"}, "a until b", "p25 p25 p25 f35");
  ExpectSpec({"1000", "0010"}, "a until b", "f15 f15 p25 f35");
  ExpectSpec({"0011", "1101"}, "1 |-> @(posedge c2) (a until b)",
             "p28 p28 p28 f38");
}

TEST(ClockRewriteAtARun, DISABLED_TheOperandOfAnAsynchronousAbortIsClocked) {
  for (const char* abort : {"accept_on", "reject_on"}) {
    ExpectSpec({"1011", "0000"},
               "1 |-> " + std::string(abort) + " (r) (@(posedge c2) a)",
               "f8 p18 f28 f38");
  }
}

TEST(ClockRewriteAtARun, DISABLED_TheOperandOfANamedPropertysAbortIsClocked) {
  for (const char* abort : {"accept_on", "reject_on"}) {
    ExpectNamed({"1011", "0000"}, kNoPulse,
                std::string(abort) + " (r) (@(posedge c2) a)",
                "f8 p18 f28 f38");
  }
}

TEST(ClockRewriteAtARun, DISABLED_AnAbortBetweenTwoClocksTicksActsThere) {
  ExpectCounts({"1111", "0000"}, {26, 1},
               "1 |-> accept_on (r) (@(posedge c2) a)", 1, 3);
  ExpectCounts({"0000", "0000"}, {26, 1},
               "1 |-> reject_on (r) (@(posedge c2) a)", 3, 1);
}

}  // namespace
