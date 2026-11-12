#include <gtest/gtest.h>

#include <cstddef>
#include <functional>
#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "helpers_sampling_bench.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(CycleDelayConcat, ParenthesizedRepetitionSequenceRegisters) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b;\n"
      "  sequence rep;\n"
      "    @(posedge clk) (a ##1 b)[*2];\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_NE(f.ctx.FindSequenceDecl("rep"), nullptr);
}

TEST(CycleDelayConcat, NamedSequenceWithConcatRegisters) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b, c;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b ##2 c;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_NE(f.ctx.FindSequenceDecl("abc"), nullptr);
  auto* ep = f.ctx.FindVariable("__seq_abc");
  ASSERT_NE(ep, nullptr);
  EXPECT_TRUE(ep->is_event);
}

std::string SequenceSource(const std::string& body, const std::string& gnt_from,
                           const std::string& gnt_to) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic req = 0;\n"
         "  logic gnt = 0;\n"
         "  int hits = 0;\n"
         "  int last = 0;\n"
         "  localparam int P = 4;\n"
         "  always #5 clk = ~clk;\n"
         "  sequence s;\n"
         "    @(posedge clk) " +
         body +
         ";\n"
         "  endsequence\n"
         "  initial begin\n"
         "    #10 req = 1;\n"
         "    #10 req = 0;\n"
         "  end\n"
         "  initial begin\n"
         "    #" +
         gnt_from + " gnt = 1;\n    #" + gnt_to +
         " gnt = 0;\n"
         "    #30 $finish;\n"
         "  end\n"
         "  initial forever begin\n"
         "    wait (s.triggered);\n"
         "    hits = hits + 1;\n"
         "    last = $time;\n"
         "    @(posedge clk);\n"
         "  end\n"
         "endmodule\n";
}

TEST(CycleDelayConcat, DelayOfTwoReadsTheSecondSubsequentTick) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceSource("req ##2 gnt", "30", "10"), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
  SimFixture g;
  auto* none =
      RunAndFindVar(SequenceSource("req ##1 gnt", "30", "10"), g, "hits");
  ASSERT_NE(none, nullptr);
  EXPECT_EQ(none->value.ToUint64(), 0u);
}

TEST(CycleDelayConcat, DelayOfZeroReadsTheSameTick) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceSource("req ##0 gnt", "10", "10"), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 15u);
}

TEST(CycleDelayConcat, DelayRangeEndsAtEveryTickInTheWindow) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceSource("req ##[2:4] gnt", "30", "40"), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
}

TEST(CycleDelayConcat, UnboundedRangeReachesADistantTick) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceSource("req ##[1:$] gnt", "60", "10"), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 65u);
  SimFixture g;
  auto* plus =
      RunAndFindVar(SequenceSource("req ##[+] gnt", "60", "10"), g, "hits");
  ASSERT_NE(plus, nullptr);
  EXPECT_EQ(plus->value.ToUint64(), 1u);
}

TEST(CycleDelayConcat, StarRangeIncludesTheSameTick) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceSource("req ##[*] gnt", "10", "10"), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 15u);
}

TEST(CycleDelayConcat, AParameterBoundIsItsValue) {
  for (const char* body :
       {"req ##P gnt", "req ##(P) gnt", "req ##[P:P+1] gnt"}) {
    SimFixture f;
    auto* hits = RunAndFindVar(SequenceSource(body, "50", "10"), f, "hits");
    ASSERT_NE(hits, nullptr) << body;
    EXPECT_EQ(hits->value.ToUint64(), 1u) << body;
    EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u) << body;
  }
}

struct Wires {
  const char* a;
  const char* b;
  const char* c = "0";
  const char* d = "0";
};

std::string TickBench(const std::string& items, const Wires& wires,
                      const std::string& outside = "",
                      const char* finish = "58") {
  return outside +
         "module top;\n"
         "  logic clk = 0;\n"
         "  int t = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(negedge clk) t++;\n"
         "  wire a = " +
         wires.a + ";\n  wire b = " + wires.b + ";\n  wire c = " + wires.c +
         ";\n  wire d = " + wires.d +
         ";\n"
         "  " +
         items +
         "\n"
         "  initial #" +
         finish +
         " $finish;\n"
         "endmodule\n";
}

std::string Covered(const std::string& property) {
  return "cover property (" + property + ") $display(\"E%0t\", $time);";
}

std::string Asserted(const std::string& property) {
  return "assert property (" + property +
         ") $display(\"E%0t pass\", $time); else $display(\"E%0t fail\", "
         "$time);";
}

std::string Shown(const std::string& property) {
  return "sequence s; @(posedge clk) " + property + "; endsequence\n  " +
         Covered("s");
}

struct Shorthand {
  const char* shorthand;
  const char* range;
};

const Shorthand kStar{"##[*]", "##[0:$]"};
const Shorthand kPlus{"##[+]", "##[1:$]"};

std::string Spelled(const std::string& pattern, const char* delay) {
  std::string out = pattern;
  for (std::size_t at = out.find("##?"); at != std::string::npos;
       at = out.find("##?", at)) {
    out.replace(at, 3, delay);
  }
  return out;
}

void ExpectBothEnd(const std::function<std::string(const std::string&)>& run,
                   const std::string& pattern, const Shorthand& form,
                   const char* ends) {
  ExpectLines(run(Spelled(pattern, form.shorthand)), "E", ends);
  ExpectLines(run(Spelled(pattern, form.range)), "E", ends);
}

std::function<std::string(const std::string&)> Declared(const Wires& wires) {
  return [=](const std::string& property) {
    return TickBench(Shown(property), wires);
  };
}

TEST(UnboundedDelayShorthand, AStarDelayReachesADistantTick) {
  ExpectBothEnd(Declared({"t == 1", "t == 5"}), "a ##? b", kStar, "55");
}

TEST(UnboundedDelayShorthand, AStarDelayEndsAtTheSameTickAndAPlusNever) {
  ExpectBothEnd(Declared({"t == 1", "t == 1"}), "a ##? b", kStar, "15");
  ExpectBothEnd(Declared({"t == 1", "t == 1"}), "a ##? b", kPlus, "");
}

TEST(UnboundedDelayShorthand, ALeadingStarStartsAtTheFirstTickAndAPlusLater) {
  ExpectBothEnd(Declared({"t == 0", "0"}), "##? a", kStar, "5");
  ExpectBothEnd(Declared({"t == 0", "0"}), "##? a", kPlus, "");
  ExpectBothEnd(Declared({"t == 3", "0"}), "##? a", kStar, "35 35 35 35");
  ExpectBothEnd(Declared({"t == 3", "0"}), "##? a", kPlus, "35 35 35");
}

TEST(UnboundedDelayShorthand, ASequenceOperandStartsWhereTheRangeAllows) {
  const auto kRun =
      Declared({"t == 1", "t == 2", "t == 2 || t == 4", "t == 3 || t == 5"});
  ExpectBothEnd(kRun, "a ##1 b ##? (c ##1 d)", kStar, "35");
  ExpectBothEnd(kRun, "a ##1 b ##? (c ##1 d)", kPlus, "55");
}

TEST(UnboundedDelayShorthand, AnAssertionPassesWhereTheRangeDoes) {
  const auto kRun = [](const std::string& property) {
    return TickBench(Asserted("@(posedge clk) " + property),
                     {"t == 1", "t == 1"});
  };
  ExpectBothEnd(kRun, "a ##? b", kStar,
                "5 fail 15 pass 25 fail 35 fail 45 fail 55 fail");
  ExpectBothEnd(kRun, "a ##? b", kPlus,
                "5 fail 25 fail 35 fail 45 fail 55 fail");
}

TEST(UnboundedDelayShorthand, ACoverStatementMatchesWhereTheRangeDoes) {
  const auto kRun = [](const std::string& property) {
    return TickBench(Covered("@(posedge clk) " + property),
                     {"t == 1", "t == 1 || t == 3"});
  };
  ExpectBothEnd(kRun, "a ##? b", kStar, "15");
  ExpectBothEnd(kRun, "a ##? b", kPlus, "35");
}

TEST(UnboundedDelayShorthand, ANamedPropertyBehavesAsTheRangeDoes) {
  const auto kRun = [](const std::string& property) {
    return TickBench("property p; @(posedge clk) " + property +
                         "; endproperty\n  " + Asserted("p"),
                     {"t == 1", "t == 1"});
  };
  ExpectBothEnd(kRun, "a ##? b", kStar,
                "5 fail 15 pass 25 fail 35 fail 45 fail 55 fail");
  ExpectBothEnd(kRun, "a ##? b", kPlus,
                "5 fail 25 fail 35 fail 45 fail 55 fail");
}

std::string ShorthandUnit(const char* kind, const std::string& property) {
  const bool kChecker = std::string(kind) == "checker";
  return std::string(kind) + " u_unit" +
         (kChecker ? "(logic clk, logic a, logic b)"
                   : "(input logic clk, a, b)") +
         ";\n  sequence su; @(posedge clk) " + property + "; endsequence\n  " +
         Covered("su") + "\nend" + kind + "\n";
}

TEST(UnboundedDelayShorthand, EveryPlaceEndsWhereTheRangeDoes) {
  for (const char* kind : {"interface", "program", "checker"}) {
    const auto kRun = [kind](const std::string& property) {
      return TickBench("u_unit u(clk, a, b);", {"t == 1", "t == 1"},
                       ShorthandUnit(kind, property));
    };
    ExpectBothEnd(kRun, "a ##? b", kStar, "15");
    ExpectBothEnd(kRun, "a ##? b", kPlus, "");
  }
  const auto kPackage = [](const std::string& property) {
    return TickBench(Covered("pk::ps(clk, a, b)"), {"t == 1", "t == 1"},
                     "package pk;\n  sequence ps(ck, x, y); @(posedge ck) " +
                         property + "; endsequence\nendpackage\n");
  };
  ExpectBothEnd(kPackage, "x ##? y", kStar, "15");
  ExpectBothEnd(kPackage, "x ##? y", kPlus, "");
  const auto kGenerate = [](const std::string& property) {
    return TickBench("if (1) begin : g\n    " + Shown(property) + "\n  end",
                     {"t == 1", "t == 1"});
  };
  ExpectBothEnd(kGenerate, "a ##? b", kStar, "15");
  ExpectBothEnd(kGenerate, "a ##? b", kPlus, "");
}

void ExpectEnds(const std::string& property, const Wires& wires,
                const char* ends) {
  ExpectLines(TickBench(Shown(property), wires), "E", ends);
}

TEST(CycleDelayCount, ALeadingDelayCountsFromTheStartingTick) {
  const Wires kWires{"t == 1 || t == 2 || t == 5", "0"};
  ExpectEnds("##2 a", kWires, "25 55");
  ExpectEnds("##0 a", kWires, "15 25 55");
  ExpectEnds("##[0:3] a", {"t == 4", "0"}, "45 45 45 45");
}

TEST(CycleDelayCount, ALeadingDelayEndsWhereTriggeredReadsIt) {
  ExpectLines(TickBench("sequence s; @(posedge clk) ##1 a; endsequence\n"
                        "  initial forever begin\n"
                        "    wait (s.triggered);\n"
                        "    $display(\"E%0t\", $time);\n"
                        "    @(posedge clk);\n"
                        "  end",
                        {"t == 1 || t == 2 || t == 5", "0"}),
              "E", "15 25 55");
}

TEST(CycleDelayCount, ALeadingDelayAssertionPassesTwoTicksLater) {
  ExpectLines(
      TickBench(Asserted("@(posedge clk) ##2 a"), {"t == 2 || t == 5", "0"}),
      "E", "25 pass 35 fail 45 fail 55 pass");
}

TEST(CycleDelayCount, AJoiningDelayCountsFromTheFirstSequencesEnd) {
  const Wires kWires{"t == 1", "t == 2", "t == 3", "t == 4"};
  ExpectEnds("(a ##1 b) ##1 (c ##1 d)", kWires, "45");
  ExpectEnds("(a ##1 b) ##2 (c ##1 d)", kWires, "");
}

TEST(CycleDelayCount, AJoiningDelayAssertionPassesAtTheSecondsEnd) {
  ExpectLines(TickBench(Asserted("@(posedge clk) (a ##1 b) ##1 (c ##1 d)"),
                        {"t == 0 || t == 3", "t == 1", "t == 2", "t == 3"}),
              "E", "15 fail 25 fail 35 pass 45 fail 45 fail 55 fail");
}

const char kOverlap[] = "(a ##1 b ##1 c) ##0 (d ##1 e ##1 f)";

std::string SixWires(const std::string& items, const char* d, const char* e,
                     const char* f) {
  return TickBench(
      std::string("wire e = ") + e + ", f = " + f + ";\n  " + items,
      {"t == 0 || t == 4", "t == 1", "t == 2", d});
}

TEST(CycleDelayCount, AZeroDelayOverlapsTheLastAndFirstTicks) {
  for (const char* property : {kOverlap, "a ##1 b ##1 c && d ##1 e ##1 f"}) {
    ExpectLines(SixWires(Shown(property), "t == 2", "t == 3", "t == 4"), "E",
                "45");
  }
  ExpectLines(SixWires(Shown(kOverlap), "t == 3", "t == 4", "t == 5"), "E", "");
  ExpectLines(SixWires(Shown("(a ##1 b ##1 c) ##1 (d ##1 e ##1 f)"), "t == 3",
                       "t == 4", "t == 5"),
              "E", "55");
}

TEST(CycleDelayCount, AZeroDelayAssertionPassesWhereTheOverlapEnds) {
  ExpectLines(SixWires(Asserted(std::string("@(posedge clk) ") + kOverlap),
                       "t == 2", "t == 3", "t == 4"),
              "E", "15 fail 25 fail 35 fail 45 pass 55 fail 55 fail");
}

const char kTrueMacro[] = "`define true 1'b1\n";

void ExpectMacroLines(const std::string& src, const char* expected) {
  SimFixture f;
  const std::string kOut = PreprocessAndCapture(src, f);
  EXPECT_FALSE(f.diag.HasErrors()) << src;
  EXPECT_EQ(LinesStartingWith(kOut, "E"), expected) << src << kOut;
}

TEST(CycleDelayCount, ATrueExtensionEndsThreeTicksAfterTheLast) {
  const Wires kWires{"t == 0", "t == 1", "t == 2"};
  ExpectMacroLines(
      TickBench(Shown("a ##1 b ##1 c ##3 `true"), kWires, kTrueMacro), "55");
  ExpectEnds("a ##1 b ##1 c ##3 1'b1", kWires, "55");
  ExpectEnds("a ##1 b ##1 c", kWires, "25");
}

std::string FailsOnly(const std::string& property) {
  return "assert property (@(posedge clk) " + property +
         ") else $display(\"E%0t fail\", $time);";
}

TEST(CycleDelayCount, ATrueExtensionDelaysTheNextImplicationTick) {
  const char kExtended[] = "a ##1 b ##1 c ##3 `true |=> d";
  ExpectMacroLines(
      TickBench(FailsOnly(kExtended), {"t == 0", "t == 1", "t == 2", "t == 6"},
                kTrueMacro, "88"),
      "");
  ExpectMacroLines(
      TickBench(FailsOnly(kExtended), {"t == 0", "t == 1", "t == 2", "t == 3"},
                kTrueMacro, "88"),
      "65 fail");
  ExpectLines(TickBench(FailsOnly("a ##1 b ##1 c |=> d"),
                        {"t == 0", "t == 1", "t == 2", "t == 6"}, "", "88"),
              "E", "35 fail");
}

}  // namespace
