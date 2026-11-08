#include <gtest/gtest.h>

#include <string>

#include "elaborator/sequence_match_attach.h"
#include "fixture_simulator.h"
#include "helpers_sequence_ticks.h"

using namespace delta;

namespace {

TEST(AttachedSubroutineScheduling, RegionIsReactive) {
  EXPECT_EQ(AttachedSubroutineRegion(),
            AttachedSubroutineSchedulingRegion::kReactive);
}

TEST(AttachedSubroutineScheduling, EvaluationDoesNotAwaitCallReturn) {
  EXPECT_FALSE(AssertionEvalWaitsForAttachedSubroutine());
}

TEST(AttachedSubroutineScheduling, ByValueArgumentUsesSampledValues) {
  EXPECT_TRUE(ByValueArgumentUsesSampledValuesOfUnderlying());
}

TEST(AttachedSubroutineScheduling, ByValueArgumentMatchesSequenceEvaluation) {
  EXPECT_TRUE(ByValueArgumentValueIsConsistentWithSequenceMatch());
}

TEST(AttachedSubroutine, RunsAtTheMatchWithTheLocalsAssigned) {
  SimFixture f;
  std::string out = RunCapture(
      SequenceTickSource(
          "(te1, v = te3) ##1 (te2[->1], w = te4, $display(\"b after a with v "
          "= %h, w = %h at %0t\", v, w, $time))",
          DriveTicks({{1}, {3}, {1}, {}, {}}), "", "    logic v, w;\n"),
      f);
  EXPECT_EQ(out, "b after a with v = 1, w = 0 at 25\n$finish at time 160\n");
}

TEST(AttachedSubroutine, RunsAtEveryEndPointInListOrder) {
  SimFixture f;
  std::string out = RunCapture(
      SequenceTickSource("(te1 ##[1:2] te2, $display(\"first at %0t\", $time), "
                         "$display(\"second at %0t\", $time))",
                         DriveTicks({{1}, {2, 3}, {}, {}, {}})),
      f);
  EXPECT_EQ(out,
            "first at 15\nsecond at 15\nfirst at 25\nsecond at 25\n"
            "$finish at time 160\n");
}

TEST(AttachedSubroutine, ByValueArgumentReadsTheSampledValue) {
  SimFixture f;
  std::string out =
      RunCapture(SequenceTickSource("(te1, $display(\"k = %0d\", k))",
                                    DriveTicks({{3}, {}, {}, {}, {}}),
                                    "  int k = 0;\n"
                                    "  always @(posedge clk) k <= k + 1;\n"),
                 f);
  EXPECT_EQ(out, "k = 2\n$finish at time 160\n");
}

TEST(AttachedSubroutine, VoidFunctionIsCalledAtTheMatch) {
  SimFixture f;
  std::string out =
      RunCapture(SequenceTickSource("(te1 ##1 te2, note($time))",
                                    DriveTicks({{2}, {3}, {}, {}, {}}),
                                    "  function void note(int t);\n"
                                    "    $display(\"noted %0d\", t);\n"
                                    "  endfunction\n"),
                 f);
  EXPECT_EQ(out, "noted 25\n$finish at time 160\n");
}

TEST(AttachedSubroutine, VoidFunctionMethodIsCalledAtTheMatch) {
  SimFixture f;
  std::string out =
      RunCapture(SequenceTickSource("(te1 ##1 te2, h.note($time))",
                                    DriveTicks({{2}, {3}, {}, {}, {}}),
                                    "  class C;\n"
                                    "    function void note(int t);\n"
                                    "      $display(\"noted %0d\", t);\n"
                                    "    endfunction\n"
                                    "  endclass\n"
                                    "  C h = new;\n"),
                 f);
  EXPECT_EQ(out, "noted 25\n$finish at time 160\n");
}

std::string NoteAtEachMatch(const std::string& use) {
  return "module t;\n"
         "  logic clk = 0, v1 = 0, v2 = 1;\n"
         "  int samples = 0, hits = 0;\n"
         "  function void note(); samples++; endfunction\n"
         "  sequence s;\n"
         "    @(posedge clk) v1 ##1 (v2, note());\n"
         "  endsequence\n" +
         use +
         "  always #5 clk = ~clk;\n"
         "  initial begin #2 v1 = 1; #20 v1 = 0; #30 $finish; end\n"
         "endmodule\n";
}

TEST(AttachedSubroutine, RunsOncePerEndPointOfTheInstance) {
  SimFixture f;
  auto* samples = RunAndFindVar(
      NoteAtEachMatch("  c1: cover property (s) hits++;\n"), f, "samples");
  ASSERT_NE(samples, nullptr);
  EXPECT_EQ(samples->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("hits")->value.ToUint64(), 2u);
}

TEST(AttachedSubroutine, NeverRunsForASequenceNothingInstantiates) {
  SimFixture f;
  auto* samples = RunAndFindVar(NoteAtEachMatch(""), f, "samples");
  ASSERT_NE(samples, nullptr);
  EXPECT_EQ(samples->value.ToUint64(), 0u);
}

TEST(AttachedSubroutine, ACallWrittenWithNoArgumentsIsMadeAtTheMatch) {
  const char* const kPrelude =
      "  function void note;\n"
      "    $display(\"noted at %0t\", $time);\n"
      "  endfunction\n"
      "  class C;\n"
      "    function void note;\n"
      "      $display(\"method noted at %0t\", $time);\n"
      "    endfunction\n"
      "  endclass\n"
      "  C h = new;\n";
  SimFixture f;
  std::string out = RunCapture(
      SequenceTickSource("(te1 ##1 te2, note, h.note)",
                         DriveTicks({{2}, {3}, {}, {}, {}}), kPrelude),
      f);
  EXPECT_EQ(out, "noted at 25\nmethod noted at 25\n$finish at time 160\n");
}

}  // namespace
