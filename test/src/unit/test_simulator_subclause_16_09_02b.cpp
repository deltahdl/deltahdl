#include <gtest/gtest.h>

#include <initializer_list>
#include <string>
#include <vector>

#include "fixture_simulator.h"

using namespace delta;

namespace {

using Ticks = std::vector<std::string>;

std::string Drive(const Ticks& ticks) {
  std::string out;
  for (const std::string& high : ticks) {
    out += "    ";
    for (const char* name : {"a", "b", "c", "x"}) {
      out += std::string(name) + " = " +
             (high.find(name) != std::string::npos ? "1" : "0") + "; ";
    }
    out += "#10;\n";
  }
  return out + "    a = 0; b = 0; c = 0; x = 0;\n    #30 $finish;\n";
}

std::string Design(const std::string& outside, const std::string& decls,
                   const std::string& items, const Ticks& ticks) {
  return outside +
         "module t;\n"
         "  logic clk = 0, a = 0, b = 0, c = 0, x = 0;\n"
         "  always #5 clk = ~clk;\n" +
         decls + "  initial begin\n" + Drive(ticks) + "  end\n" + items +
         "endmodule\n";
}

std::string RunRepetition(const std::string& src) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  EXPECT_TRUE(f.diag.Diagnostics().empty()) << src;
  return out;
}

std::string Hit(const std::string& label = "hit") {
  return " $display(\"" + label + " at %0d\", $time);\n";
}

std::string Covered(const std::string& spec, const Ticks& ticks,
                    const std::string& decls = "") {
  return RunRepetition(
      Design("", decls,
             "  cover property (@(posedge clk) " + spec + ")" + Hit(), ticks));
}

std::string Hits(std::initializer_list<int> times, int finish) {
  std::string out;
  for (int time : times) out += "hit at " + std::to_string(time) + "\n";
  return out + "$finish at time " + std::to_string(finish) + "\n";
}

constexpr const char* kAb = "  sequence ab; a ##1 b; endsequence\n";

TEST(ConsecutiveRepetitionRun, MoreIterationsThanTheCountAdmitsNeverMatch) {
  const Ticks kThreeBs = {"", "a", "b", "b", "b", "c"};
  const Ticks kTwoBs = {"", "a", "b", "b", "c"};
  for (const char* spec : {"a ##1 b[*2] ##1 c", "a ##1 b[*1:2] ##1 c"}) {
    EXPECT_EQ(Covered(spec, kThreeBs), Hits({}, 90)) << spec;
    EXPECT_EQ(Covered(spec, kTwoBs), Hits({45}, 80)) << spec;
  }
}

TEST(ConsecutiveRepetitionRun, MoreRunsOfAGroupThanTheCountAdmitsNeverMatch) {
  const Ticks kTwoRuns = {"", "x", "a", "b", "a", "b", "c"};
  EXPECT_EQ(Covered("x ##1 (a ##1 b)[*1] ##1 c", kTwoRuns), Hits({}, 100));
  EXPECT_EQ(Covered("x ##1 (a ##1 b)[*2] ##1 c", kTwoRuns), Hits({65}, 100));
}

TEST(ConsecutiveRepetitionRun, AnInstanceByARangeMatchesOverEachCountOfRuns) {
  EXPECT_EQ(Covered("ab[*1:2] ##1 c", {"", "a", "b", "a", "b", "c"}, kAb),
            Hits({55, 55}, 90));
}

TEST(ConsecutiveRepetitionRun, AnUnclockedInstanceByAnExactCountInAnAssertion) {
  const Ticks kTwoRuns = {"", "a", "b", "a", "b", "c"};
  const std::string kTt = "  sequence tt(p, q); p ##1 q; endsequence\n";
  for (const char* spec : {"a |-> ab[*2] ##1 c", "a |-> tt(a, b)[*2] ##1 c"}) {
    EXPECT_EQ(
        RunRepetition(Design("", std::string(kAb) + kTt,
                             std::string("  assert property (@(posedge clk) ") +
                                 spec + ") else" + Hit("fail"),
                             kTwoRuns)),
        "fail at 55\n$finish at time 90\n")
        << spec;
  }
}

TEST(ConsecutiveRepetitionRun, AnExactCountMatchesAsTheEqualBoundedRange) {
  struct Pair {
    const char* exact;
    const char* range;
    Ticks ticks;
    int time;
    int finish;
  };
  const Pair kPairs[] = {
      {"a ##1 b[*2] ##1 c",
       "a ##1 b[*2:2] ##1 c",
       {"", "a", "b", "b", "c"},
       45,
       80},
      {"x ##1 (a ##1 b)[*2] ##1 c",
       "x ##1 (a ##1 b)[*2:2] ##1 c",
       {"", "x", "a", "b", "a", "b", "c"},
       65,
       100},
      {"ab[*2] ##1 c", "ab[*2:2] ##1 c", {"", "a", "b", "a", "b", "c"}, 55, 90},
  };
  for (const Pair& pair : kPairs) {
    EXPECT_EQ(Covered(pair.exact, pair.ticks, kAb),
              Hits({pair.time}, pair.finish))
        << pair.exact;
    EXPECT_EQ(Covered(pair.range, pair.ticks, kAb),
              Hits({pair.time}, pair.finish))
        << pair.range;
  }
}

Ticks TwoBsThenC() { return {"", "b", "b", "c"}; }
constexpr const char* kTwoBsHit = "hit at 35\n$finish at time 70\n";

TEST(ConsecutiveRepetitionRun, ASequenceDeclaredInACheckerAndAssertedThere) {
  const Ticks kPassThenFail = {"", "a", "b", "b", "c", "", "a", "b", "c"};
  constexpr const char* kExpected = "fail at 85\n$finish at time 120\n";
  EXPECT_EQ(
      RunRepetition(Design("checker ck(logic clk, logic a, logic b, logic c);\n"
                           "  sequence s; b[*2] ##1 c; endsequence\n"
                           "  a1: assert property (@(posedge clk) a |=> s) else"
                           " $display(\"fail at %0d\", $time);\n"
                           "endchecker\n",
                           "", "  ck u(clk, a, b, c);\n", kPassThenFail)),
      kExpected);
  EXPECT_EQ(
      RunRepetition(Design(
          "", "  sequence s; b[*2] ##1 c; endsequence\n",
          "  a1: assert property (@(posedge clk) a |=> s) else" + Hit("fail"),
          kPassThenFail)),
      kExpected);
}

TEST(ConsecutiveRepetitionRun, ASequenceDeclaredInAPackage) {
  const std::string kS2 = "  sequence s2(p, q); p[*2] ##1 q; endsequence\n";
  EXPECT_EQ(RunRepetition(Design(
                "package pkg;\n" + kS2 + "endpackage\n", "",
                "  cover property (@(posedge clk) pkg::s2(b, c))" + Hit(),
                TwoBsThenC())),
            kTwoBsHit);
}

TEST(ConsecutiveRepetitionRun, DISABLED_ASequenceDeclaredInTheCompilationUnit) {
  EXPECT_EQ(
      RunRepetition(Design(
          "  sequence s2(p, q); p[*2] ##1 q; endsequence\n", "",
          "  cover property (@(posedge clk) s2(b, c))" + Hit(), TwoBsThenC())),
      kTwoBsHit);
}

TEST(ConsecutiveRepetitionRun, ASequenceDeclaredInAnInterface) {
  EXPECT_EQ(RunRepetition(
                Design("interface ifc(input logic clk, b, c);\n"
                       "  sequence s; b[*2] ##1 c; endsequence\n"
                       "  cover property (@(posedge clk) s)" +
                           Hit("inside") + "endinterface\n",
                       "  ifc u(clk, b, c);\n",
                       "  cover property (@(posedge clk) u.s)" + Hit("through"),
                       TwoBsThenC())),
            "inside at 35\nthrough at 35\n$finish at time 70\n");
}

TEST(ConsecutiveRepetitionRun, ASequenceDeclaredInAProgram) {
  EXPECT_EQ(RunRepetition(Design("program pr(input logic clk, b, c);\n"
                                 "  sequence s; b[*2] ##1 c; endsequence\n"
                                 "  cover property (@(posedge clk) s)" +
                                     Hit() + "endprogram\n",
                                 "  pr p(clk, b, c);\n", "", TwoBsThenC())),
            kTwoBsHit);
}

TEST(ConsecutiveRepetitionRun, ASequenceDeclaredInAGenerateBlock) {
  const std::string kInside =
      "    sequence s; b[*2] ##1 c; endsequence\n"
      "    cover property (@(posedge clk) s)";
  EXPECT_EQ(
      RunRepetition(Design("", "",
                           "  if (1) begin : g\n" + kInside + Hit("if") +
                               "  end\n"
                               "  for (genvar k = 0; k < 1; k++) begin : f\n" +
                               kInside + Hit("for") + "  end\n",
                           TwoBsThenC())),
      "if at 35\nfor at 35\n$finish at time 70\n");
}

TEST(ConsecutiveRepetitionRun, AProceduralAssertionInAnAlwaysProcedure) {
  const std::string kAlways =
      "  always @(posedge clk)\n"
      "    assert property (@(posedge clk) x |=> a[*2] ##1 b) else" +
      Hit("fail");
  EXPECT_EQ(RunRepetition(Design("", "", kAlways, {"", "x", "a", "b"})),
            "fail at 35\n$finish at time 70\n");
  EXPECT_EQ(RunRepetition(Design("", "", kAlways, {"", "x", "a", "a", "b"})),
            "$finish at time 80\n");
}

TEST(ConsecutiveRepetitionRun, AProceduralAssertionInAnInitialProcedure) {
  const std::string kInitial =
      "  initial assert property (@(posedge clk) x |=> a[*2] ##1 b)" +
      Hit("pass") + "    else" + Hit("fail");
  EXPECT_EQ(RunRepetition(Design("", "", kInitial, {"x", "a", "b"})),
            "fail at 25\n$finish at time 60\n");
  EXPECT_EQ(RunRepetition(Design("", "", kInitial, {"x", "a", "a", "b"})),
            "pass at 35\n$finish at time 70\n");
}

TEST(StarAndPlusRun, ABooleanStarAdmitsTheEmptyMatchAndPlusDoesNot) {
  const Ticks kNoB = {"", "a", "c"};
  const Ticks kTwoBs = {"", "a", "b", "b", "c"};
  const Ticks kOneB = {"", "a", "b", "c"};
  EXPECT_EQ(Covered("a ##1 b[*] ##1 c", kNoB), Hits({25}, 60));
  EXPECT_EQ(Covered("a ##1 b[+] ##1 c", kNoB), Hits({}, 60));
  EXPECT_EQ(Covered("a ##1 b[*] ##1 c", kTwoBs), Hits({45}, 80));
  EXPECT_EQ(Covered("a ##1 b[+] ##1 c", kOneB), Hits({35}, 70));
}

TEST(StarAndPlusRun, AGroupStarAdmitsTheEmptyMatchAndPlusDoesNot) {
  const Ticks kNoRun = {"", "x", "c"};
  const Ticks kOneRun = {"", "x", "a", "b", "c"};
  EXPECT_EQ(Covered("x ##1 (a ##1 b)[*] ##1 c", kNoRun), Hits({25}, 60));
  EXPECT_EQ(Covered("x ##1 (a ##1 b)[+] ##1 c", kNoRun), Hits({}, 60));
  EXPECT_EQ(Covered("x ##1 (a ##1 b)[*] ##1 c", kOneRun), Hits({45}, 80));
  EXPECT_EQ(Covered("x ##1 (a ##1 b)[+] ##1 c", kOneRun), Hits({45}, 80));
}

TEST(StarAndPlusRun, AnInstanceStarAdmitsTheEmptyMatchAndPlusDoesNot) {
  const std::string kInner = "  sequence inner; a ##1 b; endsequence\n";
  const Ticks kNoRun = {"", "x", "c"};
  const Ticks kOneRun = {"", "x", "a", "b", "c"};
  EXPECT_EQ(Covered("x ##1 inner[*] ##1 c", kNoRun, kInner), Hits({25}, 60));
  EXPECT_EQ(Covered("x ##1 inner[+] ##1 c", kNoRun, kInner), Hits({}, 60));
  EXPECT_EQ(Covered("x ##1 inner[*] ##1 c", kOneRun, kInner), Hits({45}, 80));
  EXPECT_EQ(Covered("x ##1 inner[+] ##1 c", kOneRun, kInner), Hits({45}, 80));
}

TEST(StarAndPlusRun, EachPlaceKeepsTheEmptyCaseDifference) {
  const Ticks kNoB = {"", "a", "c"};
  constexpr const char* kStarOnly = "star at 25\n$finish at time 60\n";
  const std::string kPair =
      "  cover property (@(posedge clk) a ##1 b[*] ##1 c)" + Hit("star") +
      "  cover property (@(posedge clk) a ##1 b[+] ##1 c)" + Hit("plus");
  EXPECT_EQ(RunRepetition(Design("", "", kPair, kNoB)), kStarOnly);
  EXPECT_EQ(RunRepetition(Design("interface ifc(input logic clk, a, b, c);\n" +
                                     kPair + "endinterface\n",
                                 "  ifc u(clk, a, b, c);\n", "", kNoB)),
            kStarOnly);
  EXPECT_EQ(RunRepetition(Design("program pr(input logic clk, a, b, c);\n" +
                                     kPair + "endprogram\n",
                                 "  pr p(clk, a, b, c);\n", "", kNoB)),
            kStarOnly);
  EXPECT_EQ(
      RunRepetition(Design(
          "package pkg;\n"
          "  sequence st(p, q, r); p ##1 q[*] ##1 r; endsequence\n"
          "  sequence pl(p, q, r); p ##1 q[+] ##1 r; endsequence\n"
          "endpackage\n",
          "",
          "  cover property (@(posedge clk) pkg::st(a, b, c))" + Hit("star") +
              "  cover property (@(posedge clk) pkg::pl(a, b, c))" +
              Hit("plus"),
          kNoB)),
      kStarOnly);
}

}  // namespace
