#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

std::string PrecedenceSource(const std::string& body,
                             const std::string& drive = "") {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic a = 0;\n"
         "  logic b = 0;\n"
         "  logic c = 0;\n"
         "  logic d = 0;\n"
         "  int hits = 0;\n"
         "  int last = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  sequence rule;\n"
         "    @(posedge clk) " +
         body +
         ";\n"
         "  endsequence\n"
         "  initial begin\n" +
         (drive.empty() ? std::string("    #10 a = 1;\n"
                                      "    #10 a = 0; b = 1;\n"
                                      "    #10 b = 0;\n"
                                      "    #10 c = 1;\n"
                                      "    #10 c = 0; d = 1;\n"
                                      "    #10 d = 0;\n")
                        : drive) +
         "    #20 $finish;\n"
         "  end\n"
         "  initial forever begin\n"
         "    wait (rule.triggered);\n"
         "    hits = hits + 1;\n"
         "    last = $time;\n"
         "    @(posedge clk);\n"
         "  end\n"
         "endmodule\n";
}

TEST(SequenceOperatorPrecedence, ConcatenationBindsTighterThanOr) {
  SimFixture f;
  auto* hits = RunAndFindVar(PrecedenceSource("a ##1 b or c ##1 d"), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
  SimFixture g;
  auto* either = RunAndFindVar(PrecedenceSource("a or c"), g, "hits");
  ASSERT_NE(either, nullptr);
  EXPECT_EQ(either->value.ToUint64(), 2u);
  EXPECT_EQ(g.ctx.FindVariable("last")->value.ToUint64(), 45u);
}

TEST(SequenceOperatorPrecedence, ConcatenationBindsTighterThanAnd) {
  SimFixture f;
  auto* hits = RunAndFindVar(PrecedenceSource("a ##1 b and c",
                                              "    #10 a = 1; c = 1;\n"
                                              "    #10 a = 0; c = 0; b = 1;\n"
                                              "    #10 b = 0;\n"),
                             f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 25u);
}

TEST(SequenceOperatorPrecedence, AndBindsTighterThanOr) {
  SimFixture f;
  auto* hits = RunAndFindVar(PrecedenceSource("a and c or d",
                                              "    #10 a = 1; c = 1;\n"
                                              "    #10 a = 0; c = 0; d = 1;\n"
                                              "    #10 d = 0;\n"
                                              "    #10 d = 1;\n"
                                              "    #10 d = 0;\n"),
                             f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 45u);
}

const char kHit[] = " $display(\"hit %0t\", $time);";

std::string BenchSignals(const std::string& drive) {
  return "  logic clk = 0, a = 0, b = 0, c = 0, d = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  initial begin\n" +
         drive +
         "    #30 $finish;\n"
         "  end\n";
}

std::string BenchSource(const std::string& place, const std::string& body,
                        const std::string& drive) {
  const std::string kLocal =
      "sequence rule; @(posedge clk) " + body + "; endsequence\n";
  const std::string kFormal =
      "sequence rule(clk, a, b, c, d); @(posedge clk) " + body +
      "; endsequence\n";
  const std::string kModule = "module m;\n" + BenchSignals(drive);
  const std::string kCover = "  cover property (rule)" + std::string(kHit);
  const std::string kCoverWith =
      "  cover property (@@rule(clk, a, b, c, d))" + std::string(kHit);
  std::string with = kCoverWith;
  if (place == "package") {
    return "package pk;\n  " + kFormal + "endpackage\n" + kModule +
           "  import pk::*;\n" + with.replace(with.find("@@"), 2, "") +
           "\nendmodule\n";
  }
  if (place == "interface") {
    return "interface ifc;\n  " + kFormal + "endinterface\n" + kModule +
           "  ifc i();\n" + with.replace(with.find("@@"), 2, "i.") +
           "\nendmodule\n";
  }
  if (place == "compilation unit") {
    return kFormal + kModule + with.replace(with.find("@@"), 2, "") +
           "\nendmodule\n";
  }
  if (place == "program") {
    return "program pg(input logic clk, a, b, c, d);\n  " + kLocal + kCover +
           "\nendprogram\n" + kModule + "  pg p(clk, a, b, c, d);\nendmodule\n";
  }
  if (place == "checker") {
    return "checker ck(logic clk, logic a, logic b, logic c, logic d);\n  " +
           kLocal + kCover + "\nendchecker\n" + kModule +
           "  ck k(clk, a, b, c, d);\nendmodule\n";
  }
  if (place == "generate block") {
    return kModule + "  if (1) begin : g\n    " + kLocal + "  " + kCover +
           "\n  end\nendmodule\n";
  }
  if (place == "assertion") {
    return kModule + "  cover property (@(posedge clk) " + body + ")" + kHit +
           "\nendmodule\n";
  }
  if (place == "procedural assertion") {
    return kModule + "  always @(posedge clk) cover property (" + body + ")" +
           kHit + "\nendmodule\n";
  }
  return kModule + "  " + kLocal +
         "  initial forever begin\n"
         "    wait (rule.triggered);\n"
         "   " +
         kHit +
         "\n"
         "    @(posedge clk);\n"
         "  end\n"
         "endmodule\n";
}

std::string Hits(const std::string& place, const std::string& body,
                 const std::string& drive) {
  SimFixture f;
  return RunCapture(BenchSource(place, body, drive), f);
}

struct Grouping {
  const char* form;
  const char* right;
  const char* wrong;
  const char* drive;
};

void ExpectGroupedAs(const Grouping& g, const std::string& place = "module") {
  SCOPED_TRACE(place + ": " + g.form);
  const std::string kRight = Hits(place, g.right, g.drive);
  EXPECT_EQ(Hits(place, g.form, g.drive), kRight);
  if (g.wrong[0] != '\0') {
    EXPECT_NE(kRight, Hits(place, g.wrong, g.drive)) << g.wrong;
  } else {
    EXPECT_NE(kRight, "");
  }
}

const char kAllHighOnce[] =
    "    #10 a = 1; b = 1; c = 1;\n    #10 a = 0; b = 0; c = 0;\n";

const char kAOnTheFirstTickBOnTheSecond[] =
    "    #10 a = 1; c = 1;\n    #10 a = 0; b = 1;\n    #10 b = 0;\n"
    "    #10 c = 0;\n";

const Grouping kTighterGroupings[] = {
    {"a throughout b ##1 c", "a throughout (b ##1 c)", "(a throughout b) ##1 c",
     "    #10 a = 1; b = 1;\n    #10 a = 0; b = 0; c = 1;\n    #10 c = 0;\n"},
    {"a throughout b within c ##1 c ##1 c",
     "(a throughout b) within (c ##1 c ##1 c)",
     "a throughout (b within (c ##1 c ##1 c))",
     "    #10 c = 1;\n    #10 a = 1; b = 1;\n    #10 a = 0; b = 0;\n"
     "    #10 c = 0;\n"},
    {"a intersect b within c ##1 c", "a intersect (b within (c ##1 c))",
     "(a intersect b) within (c ##1 c)",
     "    #10 a = 1; b = 1; c = 1;\n    #10 a = 0; b = 0;\n    #10 c = 0;\n"},
    {"a and b within c ##1 c", "a and (b within (c ##1 c))",
     "(a and b) within (c ##1 c)",
     "    #10 a = 1; c = 1;\n    #10 a = 0; b = 1;\n    #10 b = 0; c = 0;\n"},
    {"a or b intersect c[*1:2]", "a or (b intersect c[*1:2])",
     "(a or b) intersect c[*1:2]", "    #10 a = 1;\n    #10 a = 0;\n"},
    {"a within b[*2]", "a within (b[*2])", "(a within b)[*2]",
     "    #10 a = 1; b = 1;\n    #10 a = 0;\n    #10 b = 0;\n"},
    {"(a ##[0:1] c) intersect b[*2]", "(a ##[0:1] c) intersect (b[*2])",
     "((a ##[0:1] c) intersect b)[*2]",
     "    #10 a = 1; b = 1;\n    #10 a = 0; c = 1;\n    #10 b = 0; c = 0;\n"},
    {"a and b[*2]", "a and (b[*2])", "(a and b)[*2]",
     "    #10 a = 1; b = 1;\n    #10 a = 0;\n    #10 b = 0;\n"},
    {"a or b[*2]", "a or (b[*2])", "(a or b)[*2]",
     "    #10 a = 1;\n    #10 a = 0; b = 1;\n    #10 b = 0;\n"}};

TEST(SequenceOperatorPrecedence, ATighterOperatorGroupsFirst) {
  for (const auto& g : kTighterGroupings) ExpectGroupedAs(g);
}

const Grouping kWithinFromTheLeft = {
    "a within b within c ##1 c ##1 c", "(a within b) within (c ##1 c ##1 c)",
    "a within (b within (c ##1 c ##1 c))", kAOnTheFirstTickBOnTheSecond};

const Grouping kChainedWithin[] = {
    kWithinFromTheLeft,
    {"a within b within c ##1 c ##1 c", "(a within b) within (c ##1 c ##1 c)",
     "",
     "    #10 c = 1;\n    #10 a = 1; b = 1;\n    #10 a = 0; b = 0;\n"
     "    #10 c = 0;\n"},
    {"a within b within c", "(a within b) within c", "", kAllHighOnce},
    {"a within b within c within c", "((a within b) within c) within c", "",
     kAllHighOnce}};

TEST(SequenceOperatorPrecedence, DISABLED_WithinAssociatesToTheLeft) {
  for (const auto& g : kChainedWithin) ExpectGroupedAs(g);
}

const Grouping kUnchangedGroupings[] = {
    {"a throughout b throughout (c ##1 c)",
     "a throughout (b throughout (c ##1 c))", "",
     "    #10 a = 1; b = 1; c = 1;\n    #20 a = 0; b = 0; c = 0;\n"},
    {"a ##[1:2] b ##1 c", "(a ##[1:2] b) ##1 c", "",
     "    #10 a = 1;\n    #10 a = 0; b = 1;\n    #10 b = 0; c = 1;\n"
     "    #10 c = 0;\n"},
    {"a intersect b intersect c", "(a intersect b) intersect c", "",
     kAllHighOnce},
    {"a and b and c", "(a and b) and c", "", kAllHighOnce},
    {"a or b or c", "(a or b) or c", "",
     "    #10 a = 1;\n    #10 a = 0; b = 1;\n    #10 b = 0; c = 1;\n"
     "    #10 c = 0;\n"},
    {"a throughout b[*2]", "(a throughout b)[*2]", "",
     "    #10 a = 1; b = 1;\n    #20 a = 0; b = 0;\n"},
    {"(a[*2])[*3]", "a[*6]", "", "    #10 a = 1;\n    #60 a = 0;\n"},
    {"(a[->1])[*2]", "a[->2]", "",
     "    #10 a = 1;\n    #10 a = 0;\n    #10 a = 1;\n    #10 a = 0;\n"}};

TEST(SequenceOperatorPrecedence, AGroupingThatChangesNoMatchIsAccepted) {
  for (const auto& g : kUnchangedGroupings) ExpectGroupedAs(g);
}

const char* const kGroupingPlaces[] = {"package",   "program",
                                       "checker",   "generate block",
                                       "assertion", "procedural assertion"};

TEST(SequenceOperatorPrecedence, ATighterOperatorGroupsFirstInEveryPlace) {
  for (const char* place : kGroupingPlaces) {
    for (const auto& g : kTighterGroupings) ExpectGroupedAs(g, place);
  }
}

TEST(SequenceOperatorPrecedence,
     DISABLED_ATighterOperatorGroupsFirstThroughAnInterfaceInstance) {
  for (const auto& g : kTighterGroupings) ExpectGroupedAs(g, "interface");
}

TEST(SequenceOperatorPrecedence,
     DISABLED_ATighterOperatorGroupsFirstInTheUnit) {
  for (const auto& g : kTighterGroupings) {
    ExpectGroupedAs(g, "compilation unit");
  }
}

const Grouping kOrOverAnIntersectThatNeverMatches = {
    "a or b intersect c ##1 c", "a or (b intersect (c ##1 c))", "",
    "    #10 a = 1; c = 1;\n    #10 a = 0;\n    #10 c = 0;\n"};

TEST(SequenceOperatorPrecedence, AnOrBelowAnIntersectMatchesInASequence) {
  for (const char* place :
       {"module", "package", "interface", "program", "checker",
        "generate block", "compilation unit", "procedural assertion"}) {
    ExpectGroupedAs(kOrOverAnIntersectThatNeverMatches, place);
  }
}

TEST(SequenceOperatorPrecedence,
     DISABLED_AnOrBelowAnIntersectMatchesInAnAssertion) {
  ExpectGroupedAs(kOrOverAnIntersectThatNeverMatches, "assertion");
}

TEST(SequenceOperatorPrecedence,
     DISABLED_WithinAssociatesToTheLeftInEveryPlace) {
  for (const char* place : kGroupingPlaces) {
    ExpectGroupedAs(kChainedWithin[0], place);
    ExpectGroupedAs(kChainedWithin[1], place);
  }
  for (const char* place : {"interface", "compilation unit"}) {
    ExpectGroupedAs(kChainedWithin[0], place);
    ExpectGroupedAs(kChainedWithin[1], place);
  }
}

}  // namespace
