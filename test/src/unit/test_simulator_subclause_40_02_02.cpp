#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_fsm_pragma_lexing.h"
#include "simulator/vpi_coverage.h"

using namespace delta;

namespace {

TEST(CoverageNomenclature, AssertionCoverageIsWhetherItHasSucceeded) {
  AssertionCoverageCounters succeeded;
  succeeded.attempts = 4;
  succeeded.successes = 2;

  AssertionCoverageCounters never_succeeded;
  never_succeeded.attempts = 4;
  never_succeeded.vacuous_successes = 4;

  EXPECT_TRUE(AssertionCovered(succeeded));
  EXPECT_FALSE(AssertionCovered(never_succeeded));

  EXPECT_EQ(AssertAttemptCovered(succeeded), 4u);
  EXPECT_EQ(AssertSuccessCovered(succeeded), 2u);
  EXPECT_EQ(AssertFailureCovered(succeeded), 0u);
}

TEST(CoverageNomenclature, FsmCoverageCountsTheStatesReached) {
  EntityCoverage fsm;
  fsm.total = 5;
  fsm.covered = 3;

  EXPECT_EQ(CoveredEntityCount(fsm), 3u);
  EXPECT_EQ(CoveredMax(CoverageHandleKind::kAggregate, fsm), 5u);

  EntityCoverage one_state;
  one_state.total = 5;
  one_state.covered = 1;
  EXPECT_EQ(CoveredMax(CoverageHandleKind::kFsmState, one_state), 1u);
}

TEST(CoverageNomenclature, FsmExtractionIsForcedByThePragma) {
  auto pragmas =
      CollectFsmPragmas("/* tool state_vector cur_state enum state_e */");

  ASSERT_EQ(pragmas.size(), 1u);
  EXPECT_EQ(pragmas[0].signal, "cur_state");
  EXPECT_TRUE(pragmas[0].has_enum);
  EXPECT_EQ(pragmas[0].enum_name, "state_e");
}

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

TEST(CoverageNomenclature, StatementCoverageIsExecutionAtLeastOnce) {
  EntityCoverage executed;
  executed.total = 1;
  executed.covered = 1;
  executed.hit_count = 7;

  EntityCoverage never_executed;
  never_executed.total = 1;

  EXPECT_EQ(CoveredEntityCount(executed), 1u);
  EXPECT_EQ(CoveredEntityCount(never_executed), 0u);
  EXPECT_EQ(CoveredCount(executed), 7u);
  EXPECT_EQ(CoveredCount(never_executed), 0u);
}

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

TEST(CoverageNomenclature, AnInstanceCountsTheBitsOfItsPorts) {
  SimFixture f;
  const std::string kOut = RunCapture(
      "module leaf(input logic [1:0] p);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [1:0] v;\n"
      "  leaf u(v);\n"
      "  initial begin\n"
      "    v = 2'b00; #1 v = 2'b01;\n"
      "    #1 $display(\"%0d %0d\", $coverage_get_max(23, 10, u),\n"
      "                $coverage_get(23, 10, u));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "2 1\n");
}

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

TEST(CoverageNomenclature, AResetFsmCountsTheStateItHoldsAsReached) {
  SimFixture f;
  const std::string kOut = RunCapture(
      "module top;\n"
      "  parameter [1:0] /* tool enum a_e */ A0 = 0, A1 = 1;\n"
      "  /* tool state_vector sa enum a_e */\n"
      "  logic [1:0] sa;\n"
      "  parameter [1:0] /* tool enum b_e */ B0 = 0, B1 = 1;\n"
      "  /* tool state_vector sb enum b_e */\n"
      "  logic [1:0] sb;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    sa = A0; sb = B0; #1 sa = A1;\n"
      "    #1 r1 = $coverage_control(2, 21, 10, \"top\");\n"
      "    r2 = $coverage_control(2, 24, 10, \"top\");\n"
      "    sb = B1;\n"
      "    #1 $display(\"%0d %0d %0d %0d\", r1, r2,\n"
      "                $coverage_get(21, 10, \"top\"),\n"
      "                $coverage_get(24, 10, \"top\"));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "1 1 2 1\n");
}

TEST(CoverageNomenclature, AStoppedScopeCountsNoFurtherMoves) {
  SimFixture f;
  const std::string kOut = RunCapture(
      "module top;\n"
      "  parameter [1:0] /* tool enum fsm_e */ IDLE = 0, RUN = 1;\n"
      "  /* tool state_vector st enum fsm_e */\n"
      "  logic [1:0] st;\n"
      "  int r;\n"
      "  initial begin\n"
      "    st = IDLE; #1 r = $coverage_control(1, 24, 10, \"top\");\n"
      "    st = RUN; #1\n"
      "    $display(\"%0d %0d\", $coverage_get(24, 10, \"top\"),\n"
      "             $coverage_get(21, 10, \"top\"));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "0 2\n");
}

TEST(CoverageNomenclature, AStateParameterHoldingXIsNoLegalState) {
  SimFixture f;
  const std::string kOut = RunCapture(
      "module top;\n"
      "  parameter [1:0] /* tool enum fsm_e */ IDLE = 0, BAD = 2'bx;\n"
      "  /* tool state_vector st enum fsm_e */\n"
      "  logic [1:0] st;\n"
      "  initial $display(\"%0d\", $coverage_get_max(21, 10, \"top\"));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "1\n");
}

TEST(CoverageNomenclature, AStoppedScopeCountsNoFurtherToggles) {
  SimFixture f;
  const std::string kOut = RunCapture(
      "module top;\n"
      "  logic [1:0] v;\n"
      "  int r;\n"
      "  initial begin\n"
      "    v = 2'b00; #1 r = $coverage_control(1, 23, 10, \"top\");\n"
      "    v = 2'b11;\n"
      "    #1 $display(\"%0d %0d\", r, $coverage_get(23, 10, \"top\"));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "1 0\n");
}

}  // namespace
