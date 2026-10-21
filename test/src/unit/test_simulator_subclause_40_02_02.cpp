#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_fsm_pragma_lexing.h"
#include "simulator/vpi_coverage.h"

using namespace delta;

namespace {

// §40.2.2 "Nomenclature" defines the three coverage terms the rest of clause 40
// is written in. Assertion coverage records, assertion by assertion, whether
// each has succeeded at least once, and an implementation may also answer
// queries for finer figures such as how many attempts, successes and failures
// there were. FSM coverage counts the states of an FSM the simulation has
// reached; the standard does not oblige a tool to extract FSMs on its own, but
// gives pragmas as a standard way to make it extract one. Statement coverage
// records whether a statement has run, a statement being covered once it has
// run at least once, with the execution count queryable and the answer given
// for one statement or for a block of them, as the query asks. These tests read
// each term back out of what answers for it.

// §40.2.2, assertion coverage: whether the assertion has had a success. One
// that succeeded is covered, one that was attempted and never succeeded is not,
// and the further details the term allows for - how many attempts, successes
// and failures there were - are each a number of their own.
TEST(CoverageNomenclature, AssertionCoverageIsWhetherItHasSucceeded) {
  AssertionCoverageCounters succeeded;
  succeeded.attempts = 4;
  succeeded.successes = 2;

  AssertionCoverageCounters never_succeeded;
  never_succeeded.attempts = 4;
  never_succeeded.vacuous_successes = 4;

  EXPECT_TRUE(AssertionCovered(succeeded));
  EXPECT_FALSE(AssertionCovered(never_succeeded));

  // The further details: attempt, success and failure counts.
  EXPECT_EQ(AssertAttemptCovered(succeeded), 4u);
  EXPECT_EQ(AssertSuccessCovered(succeeded), 2u);
  EXPECT_EQ(AssertFailureCovered(succeeded), 0u);
}

// §40.2.2, FSM coverage: a number of states rather than a yes or no. An FSM
// whose simulation reached three of its five states reports three covered out
// of five coverable, which is what makes a coverage percentage of an FSM mean
// anything.
TEST(CoverageNomenclature, FsmCoverageCountsTheStatesReached) {
  EntityCoverage fsm;
  fsm.total = 5;
  fsm.covered = 3;

  EXPECT_EQ(CoveredEntityCount(fsm), 3u);
  EXPECT_EQ(CoveredMax(CoverageHandleKind::kAggregate, fsm), 5u);

  // One state of that machine is a single coverable entity, whatever the
  // machine around it holds.
  EntityCoverage one_state;
  one_state.total = 5;
  one_state.covered = 1;
  EXPECT_EQ(CoveredMax(CoverageHandleKind::kFsmState, one_state), 1u);
}

// §40.2.2, FSM coverage, the other half of the term: the standard requires no
// automatic extraction, and what it does define is the pragma a source writes
// to force a specific extraction. That pragma is read where a comment would
// otherwise be discarded.
TEST(CoverageNomenclature, FsmExtractionIsForcedByThePragma) {
  auto pragmas =
      CollectFsmPragmas("/* tool state_vector cur_state enum state_e */");

  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].signal, "cur_state");
  EXPECT_TRUE(pragmas[0].has_enum);
  EXPECT_EQ(pragmas[0].enum_name, "state_e");
}

// §40.2.2 with §40.4 and §40.3.2.2/§40.3.2.3: an FSM its pragmas declare is
// counted in the run, its maximum the legal states the parameters tagged with
// its enumeration name and its current count the distinct ones of those the
// state signal has held. A state held twice counts once, and a value that is
// no legal state counts not at all. The §40.3.1 constants are written as
// their values, `SV_COV_FSM_STATE 21 and `SV_COV_HIER 11 (#3603).
TEST(CoverageNomenclature, AnFsmCountsTheLegalStatesItsSignalReached) {
  SimFixture f;
  const std::string kOut = RunCapture(
      "module top;\n"
      "  parameter [1:0] /* tool enum fsm_e */ IDLE = 0, RUN = 1, DONE = 2;\n"
      "  /* tool state_vector st enum fsm_e */\n"
      "  logic [1:0] st;\n"
      "  initial begin\n"
      "    st = IDLE; #1 st = RUN; #1 st = IDLE; #1 st = 3; #1\n"
      "    $display(\"%0d %0d\", $coverage_get_max(21, 11, \"top\"),\n"
      "             $coverage_get(21, 11, \"top\"));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "3 2\n");
}

// §40.4.2: an FSM whose state a part-select holds reaches a state when the
// selected bits take its value, whatever the rest of the vector holds.
TEST(CoverageNomenclature, APartSelectFsmReadsOnlyItsSelectedBits) {
  SimFixture f;
  const std::string kOut = RunCapture(
      "module top;\n"
      "  parameter [1:0] /* tool enum sel_e */ A = 0, B = 3;\n"
      "  /* tool state_vector bus[5:4] sel_fsm enum sel_e */\n"
      "  logic [7:0] bus;\n"
      "  initial begin\n"
      "    bus = 8'b1011_0101; #1\n"
      "    $display(\"%0d %0d\", $coverage_get_max(21, 11, \"top\"),\n"
      "             $coverage_get(21, 11, \"top\"));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "2 1\n");
}

// §40.3.2.1: `SV_COV_STOP (1) stops collection over the scope, so a state the
// FSM reaches after it is not counted.
TEST(CoverageNomenclature, AStoppedScopeCountsNoFurtherStates) {
  SimFixture f;
  const std::string kOut = RunCapture(
      "module top;\n"
      "  parameter [1:0] /* tool enum fsm_e */ IDLE = 0, RUN = 1;\n"
      "  /* tool state_vector st enum fsm_e */\n"
      "  logic [1:0] st;\n"
      "  int r;\n"
      "  initial begin\n"
      "    st = IDLE; #1 r = $coverage_control(1, 21, 11, \"top\");\n"
      "    st = RUN; #1\n"
      "    $display(\"%0d\", $coverage_get(21, 11, \"top\"));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "1\n");
}

// §40.2.2, statement coverage: executed at least once is what covered means, so
// a statement that ran is covered however many times it ran, one that never ran
// is not, and the execution count is a separate number for the implementations
// that report it.
TEST(CoverageNomenclature, StatementCoverageIsExecutionAtLeastOnce) {
  EntityCoverage executed;
  executed.total = 1;
  executed.covered = 1;
  executed.hit_count = 7;

  EntityCoverage never_executed;
  never_executed.total = 1;

  EXPECT_EQ(CoveredEntityCount(executed), 1u);
  EXPECT_EQ(CoveredEntityCount(never_executed), 0u);
  // Covered says it ran; the hit count says how often, and the two are not the
  // same number.
  EXPECT_EQ(CoveredCount(executed), 7u);
  EXPECT_EQ(CoveredCount(never_executed), 0u);
}

// §40.2.2, statement coverage granularity: the query decides whether the answer
// is for one statement or for a block of them. The same term answers for one
// statement and for the block that holds it - the block reports how many of its
// statements are covered, out of how many it holds, where the single statement
// reports itself alone.
TEST(CoverageNomenclature, StatementGranularityFollowsTheQuery) {
  EntityCoverage block;
  block.total = 12;
  block.covered = 9;

  EntityCoverage statement;
  statement.total = 1;
  statement.covered = 1;

  EXPECT_EQ(CoveredEntityCount(block), 9u);
  EXPECT_EQ(CoveredMax(CoverageHandleKind::kAggregate, block), 12u);
  EXPECT_EQ(CoveredEntityCount(statement), 1u);
  EXPECT_EQ(CoveredMax(CoverageHandleKind::kAggregate, statement), 1u);
}

// §40.2.2, statement coverage, collected: every statement of an instance's
// procedures is one of its coverable items, and one is covered once it has
// executed. The block, its assignment, the if and its else branch, and the two
// assignments reading the figures have run when the second figure is read; the
// then branch never runs. `SV_COV_STATEMENT is 22 and `SV_COV_MODULE 10
// (#7528).
TEST(CoverageNomenclature, AnInstanceCountsTheStatementsThatRan) {
  SimFixture f;
  const std::string kOut = RunCapture(
      "module top;\n"
      "  int a, r1, r2;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    if (a == 0) a = 2;\n"
      "    else a = 3;\n"
      "    r1 = $coverage_get_max(22, 10, \"top\");\n"
      "    r2 = $coverage_get(22, 10, \"top\");\n"
      "    $display(\"%0d %0d\", r1, r2);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "8 6\n");
}

// §40.2.2, toggle coverage, collected: each bit of a signal is a coverable
// item, covered once it has held both 0 and 1. Of the four bits of `v`, the
// two that moved from 0 to 1 are covered, however often they move after; the
// x the signal starts at is neither value. `SV_COV_TOGGLE is 23 (#7529).
TEST(CoverageNomenclature, AnInstanceCountsTheBitsThatHeldBothValues) {
  SimFixture f;
  const std::string kOut = RunCapture(
      "module leaf;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    #1 v = 4'b0000; #1 v = 4'b0011; #1 v = 4'b0001;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  leaf u1();\n"
      "  initial #5 $display(\"%0d %0d\", $coverage_get_max(23, 10, u1),\n"
      "                      $coverage_get(23, 10, u1));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "4 2\n");
}

// §40.2.2, assertion coverage, collected: each assertion of an instance is a
// coverable item, covered once it has succeeded. Of the three, the assert that
// held is covered; the one that failed and the cover that never matched are
// not. `SV_COV_ASSERTION is 20 (#7530).
TEST(CoverageNomenclature, AnInstanceCountsTheAssertionsThatSucceeded) {
  SimFixture f;
  const std::string kOut = RunCapture(
      "module top;\n"
      "  logic a = 1, b = 0;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    #1 assert (a);\n"
      "    assert (b) else $display(\"failed\");\n"
      "    cover (b);\n"
      "    r1 = $coverage_get_max(20, 10, \"top\");\n"
      "    r2 = $coverage_get(20, 10, \"top\");\n"
      "    $display(\"%0d %0d\", r1, r2);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "failed\n3 1\n");
}

// §40.2.1 lists FSM transition coverage beside state coverage, kept here under
// the implementation-defined coverage type 24, which §40.3.1 leaves room for.
// Three legal states allow six distinct moves between two of them; the FSM
// makes three, IDLE to RUN twice among them, which counts once (#7531).
TEST(CoverageNomenclature, AnFsmCountsTheDistinctTransitionsItMade) {
  SimFixture f;
  const std::string kOut = RunCapture(
      "module top;\n"
      "  parameter [1:0] /* tool enum fsm_e */ IDLE = 0, RUN = 1, DONE = 2;\n"
      "  /* tool state_vector st enum fsm_e */\n"
      "  logic [1:0] st;\n"
      "  initial begin\n"
      "    st = IDLE; #1 st = RUN; #1 st = IDLE; #1 st = RUN; #1 st = DONE;\n"
      "    #1 $display(\"%0d %0d\", $coverage_get_max(24, 11, \"top\"),\n"
      "                $coverage_get(24, 11, \"top\"));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "6 3\n");
}

// §40.3.2.1 `SV_COV_RESET (2) over statement coverage: the statements that ran
// before it count as never executed, so the task's assignment, run again after
// it, is covered once more - beside the second call and the assignment that
// reads the figure, three in all (#7528).
TEST(CoverageNomenclature, AResetStatementRunsAgainCountsAsExecuted) {
  SimFixture f;
  const std::string kOut = RunCapture(
      "module top;\n"
      "  int x, r1, r2;\n"
      "  task automatic step(); x = x + 1; endtask\n"
      "  initial begin\n"
      "    step();\n"
      "    r1 = $coverage_control(2, 22, 10, \"top\");\n"
      "    step();\n"
      "    r2 = $coverage_get(22, 10, \"top\");\n"
      "    $display(\"%0d %0d\", r1, r2);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "1 3\n");
}

// §40.3.2.1 `SV_COV_RESET over toggle coverage: a reset bit has held neither
// value, so the two bits covered before it are not covered by the 1 they move
// to after it, nor is the third bit, which never held a 0 since (#7529).
TEST(CoverageNomenclature, AResetBitHasHeldNeitherValue) {
  SimFixture f;
  const std::string kOut = RunCapture(
      "module leaf;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b0000; #1 v = 4'b0011; #2 v = 4'b0111;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  leaf u1();\n"
      "  int r1, r2, r3;\n"
      "  initial begin\n"
      "    #2 r1 = $coverage_get(23, 10, u1);\n"
      "    r2 = $coverage_control(2, 23, 10, u1);\n"
      "    #2 r3 = $coverage_get(23, 10, u1);\n"
      "    $display(\"%0d %0d %0d\", r1, r2, r3);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "2 1 0\n");
}

// §40.4: an FSM is identified by the signal its pragma names, so a pragma
// naming no signal of the module identifies none, and the instance offers no
// FSM state coverage, `SV_COV_NOCOV (0) to a check (#7531).
TEST(CoverageNomenclature, APragmaNamingNoSignalIdentifiesNoFsm) {
  SimFixture f;
  const std::string kOut = RunCapture(
      "module top;\n"
      "  parameter [1:0] /* tool enum fsm_e */ IDLE = 0, RUN = 1;\n"
      "  /* tool state_vector nosuch enum fsm_e */\n"
      "  initial $display(\"%0d\", $coverage_control(3, 21, 10, \"top\"));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "0\n");
}

// §40.2.2: a deferred assertion's action, the one subroutine call §16.4
// allows, is a statement the run executes, in the Reactive region rather than
// where the assertion stands, and counts as executed once it has run. Of the
// seven statements, the function's assignment among them, all but the
// $display have run when the figure is read (#7541).
TEST(CoverageNomenclature, ADeferredAssertionsActionCountsAsExecuted) {
  SimFixture f;
  const std::string kOut = RunCapture(
      "module top;\n"
      "  int x, r;\n"
      "  function void set(); x = 1; endfunction\n"
      "  initial begin\n"
      "    assert #0 (1) set();\n"
      "    #1 r = $coverage_get(22, 10, \"top\");\n"
      "    $display(\"%0d %0d %0d\", $coverage_get_max(22, 10, \"top\"), r,\n"
      "             x);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "7 6 1\n");
}

}  // namespace
