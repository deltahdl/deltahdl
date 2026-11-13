#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <utility>
#include <vector>

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

std::string MatchDrive() { return DriveTicks({{2}, {3}, {}, {}, {}}); }

constexpr const char* kCountingK =
    "  int k = 0;\n"
    "  always @(posedge clk) k <= k + 1;\n";

TEST(AttachedTask, AModuleTaskIsCalledAtTheMatch) {
  std::string prelude = kCountingK;
  prelude +=
      "  task tk(int v);\n"
      "    $display(\"task %0d at %0t\", v, $time);\n"
      "  endtask\n"
      "  task tn;\n"
      "    $display(\"task no args at %0t\", $time);\n"
      "  endtask\n";
  SimFixture f;
  std::string out = RunCapture(
      SequenceTickSource("(te1 ##1 te2, tk(k), tn)", MatchDrive(), prelude), f);
  EXPECT_EQ(out, "task 2 at 25\ntask no args at 25\n$finish at time 160\n");
}

TEST(AttachedTask, TaskMethodsAreCalledAtTheMatch) {
  std::string prelude = kCountingK;
  prelude +=
      "  class C;\n"
      "    task tm(int v);\n"
      "      $display(\"task method %0d at %0t\", v, $time);\n"
      "    endtask\n"
      "    static task smt(int v);\n"
      "      $display(\"static task method %0d at %0t\", v, $time);\n"
      "    endtask\n"
      "  endclass\n"
      "  C h = new;\n";
  SimFixture f;
  std::string out =
      RunCapture(SequenceTickSource("(te1 ##1 te2, h.tm(k), C::smt(k))",
                                    MatchDrive(), prelude),
                 f);
  EXPECT_EQ(out,
            "task method 2 at 25\nstatic task method 2 at 25\n"
            "$finish at time 160\n");
}

TEST(AttachedTask, ATaskReachedThroughAScopeIsCalledAtTheMatch) {
  std::string outside =
      "package P;\n"
      "  task pt(int v);\n"
      "    $display(\"package task %0d at %0t\", v, $time);\n"
      "  endtask\n"
      "endpackage\n"
      "task ut(int v);\n"
      "  $display(\"unit task %0d at %0t\", v, $time);\n"
      "endtask\n"
      "module sub;\n"
      "  task st(int v);\n"
      "    $display(\"instance task %0d at %0t\", v, $time);\n"
      "  endtask\n"
      "endmodule\n";
  std::string prelude = kCountingK;
  prelude +=
      "  import P::*;\n"
      "  sub u();\n";
  SimFixture f;
  std::string out = RunCapture(
      outside + SequenceTickSource("(te1 ##1 te2, P::pt(k), pt(k), ut(k),"
                                   " u.st(k))",
                                   MatchDrive(), prelude),
      f);
  EXPECT_EQ(out,
            "package task 2 at 25\npackage task 2 at 25\nunit task 2 at 25\n"
            "instance task 2 at 25\n$finish at time 160\n");
}

TEST(AttachedTask, ATaskInANamedSequenceACoverInstantiatesIsCalled) {
  std::string prelude = kCountingK;
  prelude +=
      "  task tk(int v);\n"
      "    $display(\"named %0d at %0t\", v, $time);\n"
      "  endtask\n"
      "  sequence sn;\n"
      "    @(posedge clk) te1 ##1 (te2, tk(k));\n"
      "  endsequence\n"
      "  c1: cover property (sn);\n";
  SimFixture f;
  std::string out =
      RunCapture(SequenceTickSource("te5", MatchDrive(), prelude), f);
  EXPECT_EQ(out, "named 2 at 25\n$finish at time 160\n");
}

size_t Occurrences(const std::string& out, const std::string& line) {
  size_t count = 0;
  for (size_t at = out.find(line); at != std::string::npos;
       at = out.find(line, at + 1)) {
    ++count;
  }
  return count;
}

TEST(AttachedTask, ATaskAttachedInEachPlaceIsCalledAtTheMatch) {
  std::string outside =
      "package P;\n"
      "  task pt(int v);\n"
      "    $display(\"checker task %0d at %0t\", v, $time);\n"
      "  endtask\n"
      "endpackage\n"
      "interface ifc(input logic clk, te1, te2);\n"
      "  task it;\n"
      "    $display(\"interface task at %0t\", $time);\n"
      "  endtask\n"
      "  c1: cover property (@(posedge clk) (te1 ##1 te2, it));\n"
      "endinterface\n"
      "program pg(input logic clk, te1, te2);\n"
      "  task pgt;\n"
      "    $display(\"program task at %0t\", $time);\n"
      "  endtask\n"
      "  c2: cover property (@(posedge clk) (te1 ##1 te2, pgt));\n"
      "endprogram\n"
      "checker ck(logic clk, logic te1, logic te2);\n"
      "  c3: cover property (@(posedge clk) (te1 ##1 te2, P::pt(3)));\n"
      "endchecker\n";
  std::string prelude =
      "  ifc i(clk, te1, te2);\n"
      "  pg p(clk, te1, te2);\n"
      "  ck k(clk, te1, te2);\n"
      "  if (1) begin : g\n"
      "    task gt;\n"
      "      $display(\"generate task at %0t\", $time);\n"
      "    endtask\n"
      "    c4: cover property (@(posedge clk) (te1 ##1 te2, gt));\n"
      "  end\n"
      "  task at;\n"
      "    $display(\"procedural task at %0t\", $time);\n"
      "  endtask\n"
      "  class C;\n"
      "    task tm;\n"
      "      $display(\"procedural task method at %0t\", $time);\n"
      "    endtask\n"
      "  endclass\n"
      "  C h = new;\n"
      "  always @(posedge clk) c5: cover property ((te1 ##1 te2, at, h.tm));\n";
  SimFixture f;
  std::string out =
      RunCapture(outside + SequenceTickSource("te5", MatchDrive(), prelude), f);
  for (const char* line :
       {"interface task at 25\n", "program task at 25\n",
        "checker task 3 at 25\n", "generate task at 25\n",
        "procedural task at 25\n", "procedural task method at 25\n"}) {
    EXPECT_EQ(Occurrences(out, line), 1u) << line << out;
  }
}

std::string RunStatements(const std::string& prelude, const std::string& drive,
                          const std::string& outside = "") {
  SimFixture f;
  return RunCapture(outside + SequenceTickSource("te5", drive, prelude), f);
}

void ExpectLines(const std::string& out,
                 const std::vector<std::pair<std::string, size_t>>& lines) {
  for (const auto& [line, count] : lines) {
    EXPECT_EQ(Occurrences(out, line + "\n"), count) << line << "\n" << out;
  }
}

std::string Call(const std::string& tag) {
  return "$display(\"" + tag + " at %0t\", $time)";
}

TEST(AttachedEndPoint,
     DISABLED_ALoneBooleanGroupAsTheWholePropertyRunsItsCall) {
  std::string out = RunStatements(
      "  default clocking @(posedge clk); endclocking\n"
      "  a1: assert property (@(posedge clk) (te1, " +
          Call("assert") +
          ")) else;\n"
          "  m1: assume property (@(posedge clk) (te1, " +
          Call("assume") +
          ")) else;\n"
          "  c1: cover property (@(posedge clk) (te1, " +
          Call("cover") +
          "));\n"
          "  c2: cover property ((te1, " +
          Call("default") +
          "));\n"
          "  c3: cover property (@(posedge clk) (te1 or te2, " +
          Call("either") + "));\n",
      DriveTicks({{2}, {3}}));
  ExpectLines(out, {{"assert at 15", 1},
                    {"assume at 15", 1},
                    {"cover at 15", 1},
                    {"default at 15", 1},
                    {"either at 15", 1},
                    {"either at 25", 1}});
}

TEST(AttachedEndPoint,
     DISABLED_ALoneBooleanGroupAsAPropertyBodyOrConsequentRuns) {
  std::string out =
      RunStatements("  property p; @(posedge clk) (te1, " + Call("body") +
                        "); endproperty\n"
                        "  c1: cover property (p);\n"
                        "  c2: cover property (@(posedge clk) te2 |-> (te1, " +
                        Call("consequent") + "));\n",
                    DriveTicks({{2, 4}, {2}}));
  ExpectLines(out, {{"body at 15", 1},
                    {"body at 35", 1},
                    {"consequent at 15", 1},
                    {"consequent at 35", 0}});
}

TEST(AttachedEndPoint, AGroupSpanningTicksAsTheWholePropertyRunsAtItsEnd) {
  std::string out = RunStatements(
      "  property p; @(posedge clk) (te1 ##1 te2, " + Call("body") +
          "); endproperty\n"
          "  c1: cover property (p);\n"
          "  a1: assert property (@(posedge clk) (te1 ##1 te2, " +
          Call("whole") + ")) else;\n",
      DriveTicks({{2}, {3}}));
  ExpectLines(out, {{"body at 25", 1}, {"whole at 25", 1}, {"whole at 15", 0}});
}

TEST(AttachedEndPoint, ARepeatedGroupRunsAtEachIterationOfEachAttempt) {
  std::string out = RunStatements(
      "  c1: cover property (@(posedge clk) (te1, " + Call("twice") +
          ")[*2]);\n"
          "  c2: cover property (@(posedge clk) (te1, " +
          Call("plus") +
          ")[+] ##1 te2);\n"
          "  c3: cover property (@(posedge clk) (te1, " +
          Call("range") + ")[*1:2] ##1 te2);\n",
      DriveTicks({{2, 3}, {4}}));
  ExpectLines(out, {{"twice at 15", 1},
                    {"twice at 25", 2},
                    {"twice at 35", 0},
                    {"plus at 15", 1},
                    {"plus at 25", 2},
                    {"range at 15", 1},
                    {"range at 25", 2}});
}

TEST(AttachedEndPoint, ACallRunsAtTheGroupsEndWhateverTheRestDoes) {
  std::string out = RunStatements(
      "  c1: cover property (@(posedge clk) (te1 or te1 ##1 te2, " +
          Call("either") +
          ") ##1 te3);\n"
          "  c2: cover property (@(posedge clk) (te1, " +
          Call("failing") +
          ") ##1 te4);\n"
          "  c3: cover property (@(posedge clk) (te5, " +
          Call("never") + ") ##1 te1);\n",
      DriveTicks({{2}, {3}}));
  ExpectLines(out, {{"either at 15", 1},
                    {"either at 25", 1},
                    {"failing at 15", 1},
                    {"never at 15", 0},
                    {"never at 25", 0}});
}

TEST(AttachedEndPoint,
     DISABLED_ALoneBooleanGroupInEachDesignElementRunsItsCall) {
  std::string outside =
      "interface ifc(input logic clk, te1);\n"
      "  c1: cover property (@(posedge clk) (te1, " +
      Call("interface") +
      "));\n"
      "endinterface\n"
      "program pg(input logic clk, te1);\n"
      "  c2: cover property (@(posedge clk) (te1, " +
      Call("program") +
      "));\n"
      "endprogram\n"
      "checker ck(logic clk, logic te1);\n"
      "  c3: cover property (@(posedge clk) (te1, " +
      Call("checker") +
      "));\n"
      "endchecker\n";
  std::string out = RunStatements(
      "  ifc i(clk, te1);\n"
      "  pg p(clk, te1);\n"
      "  ck k(clk, te1);\n"
      "  if (1) begin : g\n"
      "    c4: cover property (@(posedge clk) (te1, " +
          Call("generate") + "));\n  end\n",
      DriveTicks({{2}}), outside);
  ExpectLines(out, {{"interface at 15", 1},
                    {"program at 15", 1},
                    {"checker at 15", 1},
                    {"generate at 15", 1}});
}

constexpr const char* kSuspendingTasks =
    "  logic go = 0;\n"
    "  initial #40 go = 1;\n"
    "  task tslow(string tag);\n"
    "    $display(\"%s start at %0t\", tag, $time);\n"
    "    #12 $display(\"%s done at %0t\", tag, $time);\n"
    "  endtask\n"
    "  task twait;\n"
    "    $display(\"wait start at %0t\", $time);\n"
    "    @(posedge clk) $display(\"wait done at %0t\", $time);\n"
    "  endtask\n"
    "  task tcond;\n"
    "    wait (go) $display(\"cond done at %0t\", $time);\n"
    "  endtask\n"
    "  class C;\n"
    "    task m;\n"
    "      #3 $display(\"method done at %0t\", $time);\n"
    "    endtask\n"
    "  endclass\n"
    "  C h = new;\n";

TEST(AttachedSuspension, ASuspendingTaskInAnActionBlockRunsToItsEnd) {
  std::string out =
      RunStatements(std::string(kSuspendingTasks) +
                        "  c1: cover property (@(posedge clk) te1 ##1 te2)"
                        " tslow(\"action\");\n",
                    MatchDrive());
  ExpectLines(out, {{"action start at 25", 1}, {"action done at 37", 1}});
}

TEST(AttachedSuspension, DISABLED_ASuspendingAttachedTaskRunsToItsEnd) {
  std::string out =
      RunStatements(std::string(kSuspendingTasks) +
                        "  c1: cover property (@(posedge clk) (te1 ##1 te2,"
                        " tslow(\"slow\"), twait, tcond, h.m));\n"
                        "  c2: cover property (@(posedge clk) te1 ##1 te2)"
                        " tslow(\"action\");\n",
                    MatchDrive());
  ExpectLines(out, {{"slow start at 25", 1},
                    {"wait start at 25", 1},
                    {"slow done at 37", 1},
                    {"action done at 37", 1},
                    {"wait done at 35", 1},
                    {"cond done at 40", 1},
                    {"method done at 28", 1}});
  EXPECT_LT(out.find("slow start at 25"), out.find("wait start at 25"));
}

TEST(AttachedSuspension, DISABLED_ASuspendingTaskInEachPlaceRunsToItsEnd) {
  std::string outside =
      "package pk;\n"
      "  task tq(string tag);\n"
      "    #12 $display(\"%s done at %0t\", tag, $time);\n"
      "  endtask\n"
      "endpackage\n"
      "interface ifc(input logic clk, te1, te2);\n"
      "  c1: cover property (@(posedge clk) (te1 ##1 te2,"
      " pk::tq(\"interface\")));\n"
      "endinterface\n"
      "program pg(input logic clk, te1, te2);\n"
      "  c2: cover property (@(posedge clk) (te1 ##1 te2,"
      " pk::tq(\"program\")));\n"
      "endprogram\n"
      "checker ck(logic clk, logic te1, logic te2);\n"
      "  c3: cover property (@(posedge clk) (te1 ##1 te2,"
      " pk::tq(\"checker\")));\n"
      "endchecker\n";
  std::string out = RunStatements(
      "  ifc i(clk, te1, te2);\n"
      "  pg p(clk, te1, te2);\n"
      "  ck k(clk, te1, te2);\n"
      "  sequence sa; @(posedge clk) te1 ##1 (te2, pk::tq(\"assert\"));"
      " endsequence\n"
      "  sequence sc; @(posedge clk) te1 ##1 (te2, pk::tq(\"cover\"));"
      " endsequence\n"
      "  sequence ss; @(posedge clk) te1 ##1 (te2, pk::tq(\"sequence\"));"
      " endsequence\n"
      "  a1: assert property (sa) else;\n"
      "  c4: cover property (sc);\n"
      "  c5: cover sequence (ss);\n"
      "  c6: cover property (@(posedge clk) (te1 ##1 te2,"
      " pk::tq(\"module\")));\n",
      MatchDrive(), outside);
  ExpectLines(out, {{"interface done at 37", 1},
                    {"program done at 37", 1},
                    {"checker done at 37", 1},
                    {"assert done at 37", 1},
                    {"cover done at 37", 1},
                    {"sequence done at 37", 1},
                    {"module done at 37", 1}});
}

TEST(AttachedSuspension, ThePassActionAndALaterMatchDoNotWait) {
  std::string out = RunStatements(
      std::string(kSuspendingTasks) +
          "  c1: cover property (@(posedge clk) (te1 ##1 te2,"
          " tslow(\"slow\"))) $display(\"pass at %0t\", $time);\n",
      DriveTicks({{2, 3}, {3, 4}}));
  ExpectLines(out, {{"slow start at 25", 1},
                    {"pass at 25", 1},
                    {"slow start at 35", 1},
                    {"pass at 35", 1}});
}

TEST(AttachedSuspension,
     DISABLED_ACallSuspendedByAnEarlierMatchDoesNotHoldALaterOne) {
  std::string out =
      RunStatements(std::string(kSuspendingTasks) +
                        "  c1: cover property (@(posedge clk) (te1 ##1 te2,"
                        " tslow(\"slow\")));\n",
                    DriveTicks({{2, 3}, {3, 4}}));
  ExpectLines(out, {{"slow done at 37", 1}, {"slow done at 47", 1}});
}

TEST(AttachedReactive, TheBodyReadsTheValuesTheMatchingTickSettled) {
  std::string prelude = kCountingK;
  prelude +=
      "  int j = 0;\n"
      "  always @(posedge clk) j = j + 1;\n"
      "  task automatic show(int v, ref int r);\n"
      "    $display(\"value %0d ref %0d body %0d blocking %0d\", v, r, k,"
      " j);\n"
      "  endtask\n"
      "  c1: cover property (@(posedge clk) (te1 ##1 te2, show(k, k)));\n";
  std::string out = RunStatements(prelude, MatchDrive());
  ExpectLines(out, {{"value 2 ref 3 body 3 blocking 3", 1}});
}

std::string LocalRun(const std::string& body, const std::string& locals,
                     const std::string& prelude = "") {
  SimFixture f;
  return RunCapture(SequenceTickSource(body, MatchDrive(), prelude, locals), f);
}

constexpr const char* kIntLocal = "    int v;\n";

TEST(AttachedLocal, ACallSeesTheItemsBeforeItAndNotThoseAfter) {
  std::string out = LocalRun(
      "(te1, v = 1, $display(\"first %0d\", v), v = v + 10,"
      " $display(\"second %0d\", v)) ##1 (te2, $display(\"later %0d\", v))",
      kIntLocal);
  ExpectLines(out, {{"first 1", 1}, {"second 11", 1}, {"later 11", 1}});
}

TEST(AttachedLocal, EachOperatorAheadOfACallIsSeen) {
  std::string out = LocalRun(
      "(te1, v = 2, v += 4, $display(\"plus %0d\", v), v++,"
      " $display(\"inc %0d\", v), --v, $display(\"dec %0d\", v),"
      " $display(\"sum %0d\", v + 1))",
      kIntLocal);
  ExpectLines(out, {{"plus 6", 1}, {"inc 7", 1}, {"dec 6", 1}, {"sum 7", 1}});
}

TEST(AttachedLocal, AnInitializedLocalIsSeenAheadOfAnyAssignment) {
  std::string out = LocalRun(
      "(te1, $display(\"init %0d\", v), v = v + 1, $display(\"next %0d\", v))",
      "    int v = 5;\n");
  ExpectLines(out, {{"init 5", 1}, {"next 6", 1}});
}

TEST(AttachedLocal, DISABLED_EachOrThreadEndingAtOneTickCallsWithItsValue) {
  std::string out = LocalRun(
      "((te1, v = 1) or (te1, v = 2), $display(\"same %0d\", v))", kIntLocal);
  ExpectLines(out, {{"same 1", 1}, {"same 2", 1}, {"same 3", 0}});
}

TEST(AttachedLocal, DISABLED_EachOrThreadReassigningAnInflowCallsWithItsValue) {
  std::string out = LocalRun(
      "((te1, v = 1) ##1 ((te2, v = v + 10) or (te2, v = v + 20)),"
      " $display(\"inflow %0d\", v))",
      kIntLocal);
  ExpectLines(out, {{"inflow 11", 1}, {"inflow 21", 1}, {"inflow 31", 0}});
}

TEST(AttachedLocal, EachOrThreadEndingAtItsOwnTickCallsWithItsValue) {
  std::string out = LocalRun(
      "((te1, v = 1) or (te1 ##1 te2, v = 2),"
      " $display(\"end %0d at %0t\", v, $time))",
      kIntLocal);
  ExpectLines(out, {{"end 1 at 15", 1}, {"end 2 at 25", 1}});
}

TEST(AttachedLocal, ALocalFlowingOutOfOneAndOrIntersectOperandIsSeen) {
  std::string out = LocalRun(
      "((te1, v = 1) and (te1 ##1 te2), $display(\"and %0d at %0t\", v,"
      " $time)) or (((te1, w = 3) ##1 te2) intersect (te1 ##1 1),"
      " $display(\"intersect %0d at %0t\", w, $time))",
      "    int v, w;\n");
  ExpectLines(out, {{"and 1 at 25", 1}, {"intersect 3 at 25", 1}});
}

TEST(AttachedLocal, LocalFormalsReachTheCall) {
  std::string out = LocalRun(
      "(so(v) ##1 te2, $display(\"out %0d\", v)) or si(4)", kIntLocal,
      "  sequence so(local output int o); (te1, o = 7); endsequence\n"
      "  sequence si(local input int i);\n"
      "    (te1, $display(\"in %0d\", i), i = i + 1, $display(\"in2 %0d\","
      " i));\n"
      "  endsequence\n");
  ExpectLines(out, {{"out 7", 1}, {"in 4", 1}, {"in2 5", 1}});
}

TEST(AttachedLocal, APropertyLocalReachesACallInItsBody) {
  std::string out =
      LocalRun("te5", "",
               "  property pp;\n"
               "    int v;\n"
               "    (te1, v = 9) |-> ##1 (te2, $display(\"prop %0d\", v));\n"
               "  endproperty\n"
               "  a1: assert property (@(posedge clk) pp);\n");
  ExpectLines(out, {{"prop 9", 1}});
}

TEST(AttachedLocal, EachCalleeKindReceivesTheLocal) {
  std::string out =
      LocalRun("(te1, v = 3, fv(v), tv(v), h.mv(v))", kIntLocal,
               "  function void fv(int x); $display(\"function %0d\", x);"
               " endfunction\n"
               "  task tv(int x); $display(\"task %0d\", x); endtask\n"
               "  class C;\n"
               "    function void mv(int x); $display(\"method %0d\", x);"
               " endfunction\n"
               "  endclass\n"
               "  C h = new;\n");
  ExpectLines(out, {{"function 3", 1}, {"task 3", 1}, {"method 3", 1}});
}

std::string LocalSequence(const std::string& tag, const std::string& name) {
  return "  sequence " + name +
         ";\n"
         "    int v;\n"
         "    @(posedge clk) (te1, v = 3) ##1 (te2, $display(\"" +
         tag +
         " %0d\", v));\n"
         "  endsequence\n";
}

std::string LocalElementPlaces() {
  return "package P;\n"
         "  sequence ps(logic clk, logic te1, logic te2);\n"
         "    int v;\n"
         "    @(posedge clk) (te1, v = 3) ##1 (te2, $display(\"package %0d\","
         " v));\n"
         "  endsequence\n"
         "endpackage\n"
         "interface ifc(input logic clk, te1, te2);\n" +
         LocalSequence("interface", "s1") +
         "  c1: cover property (s1);\n"
         "endinterface\n"
         "program pg(input logic clk, te1, te2);\n" +
         LocalSequence("program", "s2") +
         "  c2: cover property (s2);\n"
         "endprogram\n"
         "checker ck(logic clk, logic te1, logic te2);\n" +
         LocalSequence("checker", "s3") +
         "  c3: cover property (s3);\n"
         "endchecker\n";
}

void ExpectOnlyValue(const std::string& out, const std::string& tag,
                     const std::string& value) {
  size_t right = Occurrences(out, tag + " " + value + "\n");
  EXPECT_GT(right, 0u) << tag << "\n" << out;
  EXPECT_EQ(Occurrences(out, tag + " "), right) << tag << "\n" << out;
}

TEST(AttachedLocal, ALocalReachesTheCallInEachPlace) {
  std::string prelude =
      "  ifc i(clk, te1, te2);\n"
      "  pg p(clk, te1, te2);\n"
      "  ck k(clk, te1, te2);\n"
      "  c4: cover property (P::ps(clk, te1, te2));\n"
      "  clocking cb @(posedge clk);\n"
      "    sequence sk; int v; (te1, v = 3) ##1 (te2,"
      " $display(\"clocking %0d\", v)); endsequence\n"
      "  endclocking\n"
      "  c5: cover property (cb.sk);\n"
      "  if (1) begin : g\n" +
      LocalSequence("generate", "sg") +
      "    c6: cover property (sg);\n"
      "  end\n";
  std::string out = RunStatements(prelude, MatchDrive(), LocalElementPlaces());
  for (const char* tag :
       {"package", "interface", "program", "checker", "clocking", "generate"}) {
    ExpectOnlyValue(out, tag, "3");
  }
}

TEST(AttachedLocal, DISABLED_ALocalReachesTheCallInACompilationUnitSequence) {
  std::string unit =
      "sequence us(logic clk, logic te1, logic te2);\n"
      "  int v;\n"
      "  @(posedge clk) (te1, v = 3) ##1 (te2, $display(\"unit %0d\", v));\n"
      "endsequence\n";
  std::string out = RunStatements("  c1: cover property (us(clk, te1, te2));\n",
                                  MatchDrive(), unit);
  ExpectOnlyValue(out, "unit", "3");
}

std::string CallingSequences(const std::string& uses) {
  return "package P;\n"
         "  sequence ps(logic c, logic a, logic b); @(posedge c) a ##1 (b,"
         " $display(\"package\")); endsequence\n"
         "endpackage\n"
         "sequence us(logic c, logic a, logic b); @(posedge c) a ##1 (b,"
         " $display(\"unit\")); endsequence\n"
         "interface ifc(input logic clk, te1, te2);\n"
         "  sequence s1; @(posedge clk) te1 ##1 (te2, $display(\"interface\"));"
         " endsequence\n" +
         std::string(uses.empty() ? "" : "  c1: cover property (s1);\n") +
         "endinterface\n"
         "program pg(input logic clk, te1, te2);\n"
         "  sequence s2; @(posedge clk) te1 ##1 (te2, $display(\"program\"));"
         " endsequence\n" +
         std::string(uses.empty() ? "" : "  c2: cover property (s2);\n") +
         "endprogram\n"
         "checker ck(logic clk, logic te1, logic te2);\n"
         "  sequence s3; @(posedge clk) te1 ##1 (te2, $display(\"checker\"));"
         " endsequence\n" +
         std::string(uses.empty() ? "" : "  c3: cover property (s3);\n") +
         "endchecker\n";
}

std::string CallingPrelude(const std::string& uses) {
  return "  ifc i(clk, te1, te2);\n"
         "  pg p(clk, te1, te2);\n"
         "  ck k(clk, te1, te2);\n"
         "  if (1) begin : g\n"
         "    sequence s4; @(posedge clk) te1 ##1 (te2,"
         " $display(\"generate\")); endsequence\n" +
         std::string(uses.empty() ? "" : "    c4: cover property (s4);\n") +
         "  end\n"
         "  clocking cb @(posedge clk);\n"
         "    sequence s5; te1 ##1 (te2, $display(\"clocking\")); endsequence\n"
         "  endclocking\n"
         "  property p6; @(posedge clk) te1 ##1 (te2, $display(\"property\"));"
         " endproperty\n" +
         uses;
}

TEST(AttachedEndPoint,
     DISABLED_ASequenceNothingInstantiatesRunsNoCallAnywhere) {
  std::string out =
      RunStatements(CallingPrelude(""), MatchDrive(), CallingSequences(""));
  for (const char* tag : {"package", "unit", "interface", "program", "checker",
                          "generate", "clocking", "property"}) {
    EXPECT_EQ(Occurrences(out, tag), 0u) << tag << out;
  }
}

TEST(AttachedEndPoint, DISABLED_AnInstanceInEachPlaceRunsItsCallOncePerMatch) {
  std::string uses =
      "  c0: cover property (P::ps(clk, te1, te2));\n"
      "  c5: cover property (cb.s5);\n"
      "  c6: cover property (p6);\n";
  std::string out =
      RunStatements(CallingPrelude(uses), MatchDrive(), CallingSequences(uses));
  for (const char* tag : {"package", "interface", "program", "checker",
                          "generate", "clocking", "property"}) {
    EXPECT_EQ(Occurrences(out, tag), 1u) << tag << out;
  }
}

}  // namespace
