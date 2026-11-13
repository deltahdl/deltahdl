#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <iostream>
#include <sstream>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr const char* kExampleSignals =
    "  logic clk = 0;\n"
    "  logic clk1 = 0;\n"
    "  logic clk2 = 0;\n"
    "  int tick = 1;\n"
    "  logic a, b, c, d, e, f;\n";

constexpr const char* kExampleClocks =
    "  always #5 clk = ~clk;\n"
    "  always #10 tick = tick + 1;\n"
    "  initial begin\n"
    "    #12 clk1 = 1; #8 clk1 = 0; #7 clk1 = 1; #8 clk1 = 0;\n"
    "    #10 clk1 = 1; #5 clk1 = 0; #7 clk1 = 1; #8 clk1 = 0;\n"
    "    #7 clk1 = 1; #6 clk1 = 0;\n"
    "  end\n"
    "  initial begin\n"
    "    #8 clk2 = 1; #8 clk2 = 0; #9 clk2 = 1; #7 clk2 = 0;\n"
    "    #6 clk2 = 1; #8 clk2 = 0; #9 clk2 = 1; #7 clk2 = 0;\n"
    "    #8 clk2 = 1; #4 clk2 = 0; #4 clk2 = 1; #1 clk2 = 0;\n"
    "  end\n"
    "  assign a = tick inside {1, 2};\n"
    "  assign b = tick inside {3, 5};\n"
    "  assign d = tick inside {6, 7};\n"
    "  assign e = tick inside {3};\n";

constexpr const char* kThenStimulus =
    "  assign c = tick inside {3, 4, 6};\n"
    "  assign f = tick inside {4};\n";

constexpr const char* kElseStimulus =
    "  assign c = tick inside {4, 6};\n"
    "  initial begin f = 0; #36 f = 1; #4 f = 0; end\n";

constexpr const char* kExampleDeclarations =
    "  sequence s1;\n"
    "    a ##1 b;\n"
    "  endsequence\n"
    "  sequence s2;\n"
    "    c ##1 d;\n"
    "  endsequence\n"
    "  sequence mult_s;\n"
    "    @(posedge clk) a ##1 @(posedge clk1) s1 ##1 @(posedge clk2) s2;\n"
    "  endsequence\n"
    "  property mult_p1;\n"
    "    @(posedge clk) a ##1 @(posedge clk1) s1 ##1 @(posedge clk2) s2;\n"
    "  endproperty\n"
    "  property mult_p2;\n"
    "    mult_s;\n"
    "  endproperty\n"
    "  property mult_p3;\n"
    "    @(posedge clk) a ##1 @(posedge clk1) s1 |=> @(posedge clk2) s2;\n"
    "  endproperty\n"
    "  property mult_p6;\n"
    "    mult_s |=> mult_s;\n"
    "  endproperty\n"
    "  property mult_p7;\n"
    "    @(posedge clk) a ##1 b |-> c ##1 @(posedge clk1) d;\n"
    "  endproperty\n"
    "  property mult_p8;\n"
    "    @(posedge clk) a ##1 b |->\n"
    "      if (c)\n"
    "        (1 |=> @(posedge clk1) d)\n"
    "      else\n"
    "        e ##1 @(posedge clk2) f ;\n"
    "  endproperty\n";

constexpr const char* kUnitPlaces[] = {"module", "interface", "program",
                                       "checker"};

std::string ExampleDirective(const std::string& directive,
                             const std::string& spec) {
  std::string line =
      "  " + directive + " property (" + spec + ") $display(\"PASS\");";
  if (directive != "cover") line += " else $display(\"FAIL %0t\", $time);";
  return line + "\n";
}

std::string ExampleTop(const std::string& stimulus, const std::string& items,
                       const std::string& head) {
  return "module t;\n" + head + kExampleClocks + stimulus + items +
         "  initial #80 $finish;\n"
         "endmodule\n";
}

std::string ExampleSource(const std::string& place,
                          const std::string& directive, const std::string& spec,
                          const std::string& stimulus) {
  std::string assertion = ExampleDirective(directive, spec);
  std::string signals = kExampleSignals;
  if (place == "module") {
    return ExampleTop(stimulus, kExampleDeclarations + assertion, signals);
  }
  if (place == "generate") {
    return ExampleTop(stimulus,
                      "  if (1) begin : g\n" +
                          std::string(kExampleDeclarations) + assertion +
                          "  end\n",
                      signals);
  }
  if (place == "clocked procedural") {
    return ExampleTop(stimulus,
                      kExampleDeclarations +
                          std::string("  always @(posedge clk)") +
                          assertion.substr(1),
                      signals);
  }
  if (place == "package") {
    return "package pk;\n" + signals + kExampleDeclarations + "endpackage\n" +
           ExampleTop(stimulus, assertion, "  import pk::*;\n");
  }
  if (place == "unit") {
    return signals + kExampleDeclarations + ExampleTop(stimulus, assertion, "");
  }
  std::string header =
      place == "checker"
          ? "checker w(clk, clk1, clk2, a, b, c, d, e, f);\n"
          : place + " w(input logic clk, clk1, clk2, a, b, c, d, e, f);\n";
  return header + kExampleDeclarations + assertion + "end" + place + "\n" +
         ExampleTop(stimulus, "  w u(clk, clk1, clk2, a, b, c, d, e, f);\n",
                    signals);
}

struct ExampleCounts {
  uint64_t passes;
  uint64_t fails;
  uint64_t fail_sum;
  bool operator==(const ExampleCounts&) const = default;
};

std::ostream& operator<<(std::ostream& os, const ExampleCounts& counts) {
  return os << "{" << counts.passes << " passes, " << counts.fails
            << " fails at times summing to " << counts.fail_sum << "}";
}

ExampleCounts CountsOfExample(const std::string& src) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  f.ctx.RunFinalBlocks();
  std::cout.rdbuf(old_buf);
  std::istringstream lines(out + captured.str());
  ExampleCounts counts{0, 0, 0};
  for (std::string line; std::getline(lines, line);) {
    if (line == "PASS") ++counts.passes;
    if (line.starts_with("FAIL ")) {
      ++counts.fails;
      counts.fail_sum += std::stoull(line.substr(5));
    }
  }
  return counts;
}

struct ExampleRow {
  const char* spec;
  const char* stimulus;
  ExampleCounts asserted;
  uint64_t covered;
};

constexpr ExampleRow kExamples[] = {{"mult_s", kThenStimulus, {1, 7, 327}, 1},
                                    {"mult_p1", kThenStimulus, {1, 7, 327}, 1},
                                    {"mult_p2", kThenStimulus, {1, 7, 327}, 1},
                                    {"mult_p3", kThenStimulus, {8, 0, 0}, 8},
                                    {"mult_p6", kThenStimulus, {7, 1, 65}, 7},
                                    {"mult_p7", kThenStimulus, {7, 1, 27}, 7},
                                    {"mult_p8", kThenStimulus, {7, 1, 27}, 7},
                                    {"mult_p8", kElseStimulus, {8, 0, 0}, 8}};

void ExpectExampleCountsIn(const std::string& place, const ExampleRow& row) {
  for (const char* directive : {"assert", "assume"}) {
    SCOPED_TRACE(place + " " + directive + " " + row.spec);
    EXPECT_EQ(CountsOfExample(
                  ExampleSource(place, directive, row.spec, row.stimulus)),
              row.asserted);
  }
  SCOPED_TRACE(place + " cover " + row.spec);
  EXPECT_EQ(
      CountsOfExample(ExampleSource(place, "cover", row.spec, row.stimulus)),
      (ExampleCounts{row.covered, 0, 0}));
}

void ExpectExampleIn(const std::string& spec, const std::string& place) {
  for (const ExampleRow& row : kExamples) {
    if (spec == row.spec) ExpectExampleCountsIn(place, row);
  }
}

template <typename Places>
void ExpectExamplesIn(const Places& places,
                      std::initializer_list<const char*> specs) {
  for (const char* place : places) {
    for (const char* spec : specs) ExpectExampleIn(spec, place);
  }
}

void ExpectExampleInEachUnit(const std::string& spec) {
  for (const char* place : kUnitPlaces) ExpectExampleIn(spec, place);
}

TEST(MulticlockExamples, TheMulticlockSequenceMatchesAcrossItsThreeClocks) {
  ExpectExampleInEachUnit("mult_s");
}

TEST(MulticlockExamples, APropertyOfAMulticlockSequenceMatchesLikeIt) {
  ExpectExampleInEachUnit("mult_p1");
}

TEST(MulticlockExamples, ANamedMulticlockSequenceIsAPropertyBody) {
  ExpectExampleInEachUnit("mult_p2");
}

TEST(MulticlockExamples, TheMulticlockImplicationReadsItsConsequentOnItsClock) {
  ExpectExampleInEachUnit("mult_p3");
}

TEST(MulticlockExamples,
     NamedMulticlockSequencesStandOnBothSidesOfAnImplication) {
  ExpectExampleInEachUnit("mult_p6");
}

TEST(MulticlockExamples, ClockFlowPutsTheUnclockedOperandsOnTheLeadingClock) {
  ExpectExampleInEachUnit("mult_p7");
}

TEST(MulticlockExamples, BothBranchesOfTheIfElseTakeTheFlowingClock) {
  ExpectExampleInEachUnit("mult_p8");
}

TEST(MulticlockExamples, TheInlineExamplesCountInAGenerateBlock) {
  ExpectExamplesIn(std::initializer_list<const char*>{"generate"},
                   {"mult_s", "mult_p1", "mult_p7", "mult_p8"});
}

TEST(MulticlockExamples,
     DISABLED_ANamedSequenceAsAGeneratePropertysBodyOrConsequentCounts) {
  ExpectExamplesIn(std::initializer_list<const char*>{"generate"},
                   {"mult_p2", "mult_p3", "mult_p6"});
}

constexpr std::initializer_list<const char*> kEveryExample = {
    "mult_s", "mult_p1", "mult_p2", "mult_p3", "mult_p6", "mult_p7", "mult_p8"};

TEST(MulticlockExamples, DISABLED_EachExampleCountsInAClockedProcedure) {
  ExpectExamplesIn(std::initializer_list<const char*>{"clocked procedural"},
                   kEveryExample);
}

TEST(MulticlockExamples,
     DISABLED_EachExampleCountsOverThePackagesOwnVariables) {
  ExpectExamplesIn(std::initializer_list<const char*>{"package"},
                   kEveryExample);
}

TEST(MulticlockExamples, DISABLED_EachExampleCountsInTheCompilationUnit) {
  ExpectExamplesIn(std::initializer_list<const char*>{"unit"}, kEveryExample);
}

}  // namespace
