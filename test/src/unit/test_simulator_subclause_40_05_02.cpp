#include <gtest/gtest.h>

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_coverage.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(CoverageInformationQueries, SuccessCoveredReportsNonvacuousSuccesses) {
  AssertionCoverageCounters c;
  c.successes = 4;
  EXPECT_EQ(AssertSuccessCovered(c), 4U);

  AssertionCoverageCounters seq;
  seq.is_cover_sequence = true;
  seq.successes = 9;
  EXPECT_EQ(AssertSuccessCovered(seq), 9U);
}

TEST(CoverageInformationQueries, StatusQueryDispatchesByProperty) {
  AssertionCoverageCounters c;
  c.attempts = 10;
  c.successes = 4;
  c.vacuous_successes = 1;
  c.disabled = 2;
  c.killed = 1;
  c.failures = 2;

  EXPECT_EQ(AssertionStatusQuery(CoverageProperty::kAssertAttemptCovered, c),
            10U);
  EXPECT_EQ(AssertionStatusQuery(CoverageProperty::kAssertSuccessCovered, c),
            4U);
  EXPECT_EQ(
      AssertionStatusQuery(CoverageProperty::kAssertVacuousSuccessCovered, c),
      1U);
  EXPECT_EQ(AssertionStatusQuery(CoverageProperty::kAssertDisableCovered, c),
            2U);
  EXPECT_EQ(AssertionStatusQuery(CoverageProperty::kAssertKillCovered, c), 1U);
  EXPECT_EQ(AssertionStatusQuery(CoverageProperty::kAssertFailureCovered, c),
            2U);
  EXPECT_EQ(AssertionStatusQuery(CoverageProperty::kStatementCoverage, c), 0U);
}

TEST(CoverageInformationQueries,
     AssertionCoveredRequiresAttemptSuccessNoFailure) {
  AssertionCoverageCounters covered;
  covered.attempts = 3;
  covered.successes = 3;
  EXPECT_TRUE(AssertionCovered(covered));

  AssertionCoverageCounters never_attempted;
  EXPECT_FALSE(AssertionCovered(never_attempted));

  AssertionCoverageCounters no_success;
  no_success.attempts = 3;
  EXPECT_FALSE(AssertionCovered(no_success));

  AssertionCoverageCounters has_failed;
  has_failed.attempts = 3;
  has_failed.successes = 2;
  has_failed.failures = 1;
  EXPECT_FALSE(AssertionCovered(has_failed));
}

TEST(CoverageInformationQueries, AssertionCoveredExcludesVacuousOnlySuccess) {
  AssertionCoverageCounters vacuous_only;
  vacuous_only.attempts = 4;
  vacuous_only.vacuous_successes = 4;
  EXPECT_FALSE(AssertionCovered(vacuous_only));
}

TEST(CoverageInformationQueries, WorkedExampleAssertionCoverageResults) {
  AssertionCoverageCounters anvr;
  EXPECT_FALSE(AssertionCovered(anvr));
  EXPECT_EQ(AssertAttemptCovered(anvr), 0U);
  EXPECT_EQ(AssertSuccessCovered(anvr), 0U);
  EXPECT_EQ(AssertFailureCovered(anvr), 0U);

  AssertionCoverageCounters aundf;
  aundf.attempts = 5;
  EXPECT_FALSE(AssertionCovered(aundf));
  EXPECT_GT(AssertAttemptCovered(aundf), 0U);
  EXPECT_EQ(AssertSuccessCovered(aundf), 0U);
  EXPECT_EQ(AssertFailureCovered(aundf), 0U);

  AssertionCoverageCounters afail;
  afail.attempts = 5;
  afail.failures = 5;
  EXPECT_FALSE(AssertionCovered(afail));
  EXPECT_GT(AssertAttemptCovered(afail), 0U);
  EXPECT_EQ(AssertSuccessCovered(afail), 0U);
  EXPECT_GT(AssertFailureCovered(afail), 0U);

  AssertionCoverageCounters apass;
  apass.attempts = 5;
  apass.successes = 5;
  EXPECT_TRUE(AssertionCovered(apass));
  EXPECT_GT(AssertAttemptCovered(apass), 0U);
  EXPECT_GT(AssertSuccessCovered(apass), 0U);
  EXPECT_EQ(AssertFailureCovered(apass), 0U);
}

TEST(CoverageInformationQueries,
     InProgressDerivesFromAttemptsMinusConclusions) {
  AssertionCoverageCounters c;
  c.attempts = 10;
  c.successes = 3;
  c.vacuous_successes = 1;
  c.disabled = 1;
  c.killed = 1;
  c.failures = 2;
  const std::optional<std::uint64_t> kInProgress = AssertInProgress(c);
  ASSERT_TRUE(kInProgress.has_value());
  if (!kInProgress.has_value()) return;
  EXPECT_EQ(kInProgress.value(), 2U);

  AssertionCoverageCounters all_concluded;
  all_concluded.attempts = 4;
  all_concluded.successes = 4;
  const std::optional<std::uint64_t> kNone = AssertInProgress(all_concluded);
  ASSERT_TRUE(kNone.has_value());
  if (!kNone.has_value()) return;
  EXPECT_EQ(kNone.value(), 0U);
}

TEST(CoverageInformationQueries, InProgressClampsWhenOutcomesExceedAttempts) {
  AssertionCoverageCounters c;
  c.attempts = 2;
  c.successes = 3;
  c.failures = 2;
  const std::optional<std::uint64_t> kInProgress = AssertInProgress(c);
  ASSERT_TRUE(kInProgress.has_value());
  if (!kInProgress.has_value()) return;
  EXPECT_EQ(kInProgress.value(), 0U);
}

TEST(CoverageInformationQueries, InProgressUndefinedForCoverSequence) {
  AssertionCoverageCounters seq;
  seq.is_cover_sequence = true;
  seq.attempts = 3;
  seq.successes = 7;
  EXPECT_FALSE(AssertInProgress(seq).has_value());
}

TEST(CoverageInformationQueries, CoveredEntityCountReportsCoveredEntities) {
  EntityCoverage e;
  e.total = 8;
  e.covered = 5;
  EXPECT_EQ(CoveredEntityCount(e), 5U);
}

TEST(CoverageInformationQueries, CoveredCountReportsHitCount) {
  EntityCoverage e;
  e.total = 8;
  e.covered = 5;
  e.hit_count = 42;
  EXPECT_EQ(CoveredCount(e), 42U);
}

TEST(CoverageInformationQueries, CoveredMaxReportsEntityTotalForAggregate) {
  EntityCoverage e;
  e.total = 8;
  e.covered = 5;
  EXPECT_EQ(CoveredMax(CoverageHandleKind::kAggregate, e), 8U);
}

TEST(CoverageInformationQueries, CoveredMaxIsOneForAssertionAndFsmStateHandle) {
  EntityCoverage e;
  e.total = 8;
  e.covered = 5;
  EXPECT_EQ(CoveredMax(CoverageHandleKind::kAssertion, e), 1U);
  EXPECT_EQ(CoveredMax(CoverageHandleKind::kFsmState, e), 1U);
}

TEST(CoverageInformationQueries, InstanceCoverageSelectsByCoverageType) {
  InstanceCoverage inst;
  inst.assertions.covered = 1;
  inst.fsm_states.covered = 2;
  inst.statements.covered = 3;
  inst.toggles.covered = 4;

  EXPECT_EQ(InstanceCoverageCount(CoverageProperty::kAssertCoverage, inst), 1U);
  EXPECT_EQ(InstanceCoverageCount(CoverageProperty::kFsmStateCoverage, inst),
            2U);
  EXPECT_EQ(InstanceCoverageCount(CoverageProperty::kStatementCoverage, inst),
            3U);
  EXPECT_EQ(InstanceCoverageCount(CoverageProperty::kToggleCoverage, inst), 4U);
  EXPECT_EQ(InstanceCoverageCount(CoverageProperty::kCovered, inst), 0U);
}

using ItemCoverageRun = VpiDesignRun;

constexpr const char* kFsmDesign =
    "module top;\n"
    "  parameter [1:0] /* tool enum fsm_e */ IDLE = 0, RUN = 1, DONE = 2;\n"
    "  /* tool state_vector st enum fsm_e */\n"
    "  logic [1:0] st;\n"
    "  initial begin\n"
    "    st = IDLE; #1 st = RUN; #1 st = IDLE;\n"
    "  end\n"
    "endmodule\n";

TEST_F(ItemCoverageRun, AnAssertionHandleReadsItsOwnTallies) {
  Run("module top;\n"
      "  logic clk = 0, a = 1, b = 0, never = 0;\n"
      "  ok: assert property (@(posedge clk) a);\n"
      "  idle: assert property (@(posedge never) a);\n"
      "  bad: assert property (@(posedge clk) b) else $display(\"bad\");\n"
      "  vac: assert property (@(posedge clk) b |-> a);\n"
      "  initial begin\n"
      "    #1 clk = 1; #1 clk = 0; #1 clk = 1; #1 clk = 0;\n"
      "  end\n"
      "endmodule\n");
  vpiHandle ok = Named(vpiAssertion, By("top"), "ok");
  vpiHandle bad = Named(vpiAssertion, By("top"), "bad");
  ASSERT_NE(ok, nullptr);
  ASSERT_NE(bad, nullptr);

  const int kAttempts = vpi_get(vpiAssertAttemptCovered, ok);
  EXPECT_GT(kAttempts, 0);
  EXPECT_EQ(vpi_get(vpiAssertSuccessCovered, ok), kAttempts);
  EXPECT_EQ(vpi_get(vpiAssertFailureCovered, ok), 0);
  EXPECT_EQ(vpi_get(vpiCovered, ok), 1);
  EXPECT_EQ(vpi_get(vpiCoveredCount, ok), kAttempts);
  EXPECT_EQ(vpi_get(vpiCoveredMax, ok), 1);
  EXPECT_EQ(vpi_get(vpiAssertVacuousSuccessCovered, ok), 0);
  EXPECT_EQ(vpi_get(vpiAssertDisableCovered, ok), 0);
  EXPECT_EQ(vpi_get(vpiAssertKillCovered, ok), 0);

  EXPECT_EQ(vpi_get(vpiAssertFailureCovered, bad), kAttempts);
  EXPECT_EQ(vpi_get(vpiAssertSuccessCovered, bad), 0);
  EXPECT_EQ(vpi_get(vpiCovered, bad), 0);
  EXPECT_EQ(vpi_get(vpiCoveredMax, bad), 1);

  vpiHandle idle = Named(vpiAssertion, By("top"), "idle");
  ASSERT_NE(idle, nullptr);
  EXPECT_EQ(vpi_get(vpiAssertAttemptCovered, idle), 0);
  EXPECT_EQ(vpi_get(vpiCovered, idle), 0);

  vpiHandle vac = Named(vpiAssertion, By("top"), "vac");
  ASSERT_NE(vac, nullptr);
  EXPECT_EQ(vpi_get(vpiAssertVacuousSuccessCovered, vac), kAttempts);
  EXPECT_EQ(vpi_get(vpiCovered, vac), 0);
}

TEST_F(ItemCoverageRun, AStatementHandleCountsTheStatementsItHolds) {
  Run("module top;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = 1;\n"
      "    if (x == 0) x = 2;\n"
      "  end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
  ASSERT_EQ(kProcs.size(), 1u);
  vpiHandle block = vpi_handle(vpiStmt, kProcs.front());
  ASSERT_NE(block, nullptr);
  EXPECT_EQ(vpi_get(vpiCoveredMax, block), 3);
  EXPECT_EQ(vpi_get(vpiCovered, block), 2);
  EXPECT_EQ(vpi_get(vpiCoveredCount, block), 2);

  const std::vector<vpiHandle> kStmts = ObjectsOf(vpiStmt, block);
  ASSERT_EQ(kStmts.size(), 2u);
  EXPECT_EQ(vpi_get(vpiCoveredMax, kStmts[1]), 2);
  EXPECT_EQ(vpi_get(vpiCovered, kStmts[1]), 1);
}

TEST_F(ItemCoverageRun, AForkHandleCountsTheStatementsItHolds) {
  Run("module top;\n"
      "  int x, y;\n"
      "  initial fork\n"
      "    x = 1;\n"
      "    y = 2;\n"
      "  join\n"
      "endmodule\n");
  const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
  ASSERT_EQ(kProcs.size(), 1u);
  vpiHandle fork = vpi_handle(vpiStmt, kProcs.front());
  ASSERT_NE(fork, nullptr);
  EXPECT_EQ(vpi_get(vpiType, fork), vpiFork);
  EXPECT_EQ(vpi_get(vpiCoveredMax, fork), 2);
  EXPECT_EQ(vpi_get(vpiCovered, fork), 2);
}

TEST_F(ItemCoverageRun, ASignalHandleCountsItsBitsAndTheirToggles) {
  Run("module top;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b0000; #1 v = 4'b0011; #1 v = 4'b0001;\n"
      "  end\n"
      "endmodule\n");
  vpiHandle v = By("top.v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(vpi_get(vpiCoveredMax, v), 4);
  EXPECT_EQ(vpi_get(vpiCovered, v), 2);
  EXPECT_EQ(vpi_get(vpiCoveredCount, v), 3);
}

TEST_F(ItemCoverageRun, APortHandleCountsItsBits) {
  Run("module leaf(input logic [1:0] p, inout wire [1:0] q);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [1:0] v;\n"
      "  wire [1:0] w = v;\n"
      "  leaf a(v, w);\n"
      "  leaf b(v, w);\n"
      "  initial begin\n"
      "    v = 2'b00; #1 v = 2'b01;\n"
      "  end\n"
      "endmodule\n");
  vpiHandle p = Named(vpiNet, By("top.a"), "p");
  vpiHandle q = Named(vpiNet, By("top.b"), "q");
  ASSERT_NE(p, nullptr);
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(vpi_get(vpiCoveredMax, p), 2);
  EXPECT_EQ(vpi_get(vpiCovered, p), 1);
  EXPECT_EQ(vpi_get(vpiCoveredMax, q), 2);
  EXPECT_EQ(vpi_get(vpiCovered, q), 1);
}

TEST_F(ItemCoverageRun, ABitHandleAnswersNoCoverage) {
  Run("module top;\n"
      "  logic [1:0] v;\n"
      "  wire [1:0] w = v;\n"
      "  initial begin\n"
      "    v = 2'b00; #1 v = 2'b11;\n"
      "  end\n"
      "endmodule\n");
  vpiHandle v = By("top.v");
  vpiHandle w = By("top.w");
  ASSERT_NE(v, nullptr);
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(vpi_get(vpiCovered, v), 2);
  EXPECT_EQ(vpi_get(vpiCovered, w), 2);
  vpiHandle v_bit = vpi_handle_by_index(v, 0);
  vpiHandle w_bit = vpi_handle_by_index(w, 0);
  ASSERT_NE(v_bit, nullptr);
  ASSERT_NE(w_bit, nullptr);
  EXPECT_EQ(vpi_get(vpiType, v_bit), vpiRegBit);
  EXPECT_EQ(vpi_get(vpiType, w_bit), vpiNetBit);
  EXPECT_EQ(vpi_get(vpiCoveredMax, v_bit), 0);
  EXPECT_EQ(vpi_get(vpiCoveredMax, w_bit), 0);
}

TEST_F(ItemCoverageRun, AnInstanceReachesItsFsms) {
  Run(kFsmDesign);
  EXPECT_EQ(NamesOf(vpiFsm, By("top")), std::vector<std::string>{"st"});
  EXPECT_EQ(KindsOf(vpiFsm, By("top")), std::vector<int>{vpiFsm});
}

constexpr const char* kLeafFsm =
    "module leaf;\n"
    "  parameter [1:0] /* tool enum fsm_e */ IDLE = 0, RUN = 1;\n"
    "  /* tool state_vector st enum fsm_e */\n"
    "  logic [1:0] st;\n"
    "endmodule\n";

TEST_F(ItemCoverageRun, AnInstanceBelowTheTopReachesItsFsms) {
  Run(std::string(kLeafFsm) +
      "module top;\n"
      "  leaf u();\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiFsm, By("top.u")), std::vector<std::string>{"st"});
}

TEST_F(ItemCoverageRun, AnInstanceInAGenerateBlockReachesItsFsms) {
  Run(std::string(kLeafFsm) +
      "module top;\n"
      "  if (1) begin : g\n"
      "    leaf u();\n"
      "  end\n"
      "endmodule\n");
  vpiHandle u = By("top.g.u");
  ASSERT_NE(u, nullptr);
  vpiHandle fsm = Named(vpiFsm, u, "st");
  ASSERT_NE(fsm, nullptr);
  vpiHandle signal = vpi_handle(vpiFsmStateExpression, fsm);
  ASSERT_NE(signal, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, signal), "top.g.u.st");
  EXPECT_EQ(NamesOf(vpiFsmStates, fsm),
            (std::vector<std::string>{"IDLE", "RUN"}));
}

TEST_F(ItemCoverageRun, AnFsmReachesTheExpressionHoldingItsState) {
  Run("module top;\n"
      "  parameter [1:0] /* tool enum fsm_e */ IDLE = 0, RUN = 1;\n"
      "  /* tool state_vector st enum fsm_e */\n"
      "  logic [1:0] st;\n"
      "  parameter [1:0] /* tool enum sel_e */ A = 0, B = 3;\n"
      "  /* tool state_vector bus[5:4] sel_fsm enum sel_e */\n"
      "  logic [7:0] bus;\n"
      "  parameter [1:0] /* tool enum cat_e */ P = 0, Q = 3;\n"
      "  /* tool state_vector {hi, lo} cat_fsm enum cat_e */\n"
      "  logic hi, lo;\n"
      "endmodule\n");
  vpiHandle st = Named(vpiFsm, By("top"), "st");
  ASSERT_NE(st, nullptr);
  vpiHandle signal = vpi_handle(vpiFsmStateExpression, st);
  ASSERT_NE(signal, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, signal), "top.st");

  vpiHandle sel = Named(vpiFsm, By("top"), "sel_fsm");
  ASSERT_NE(sel, nullptr);
  vpiHandle select = vpi_handle(vpiFsmStateExpression, sel);
  ASSERT_NE(select, nullptr);
  EXPECT_EQ(vpi_get(vpiType, select), vpiPartSelect);
  vpiHandle parent = vpi_handle(vpiParent, select);
  ASSERT_NE(parent, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, parent), "top.bus");
  s_vpi_value left = {};
  left.format = vpiIntVal;
  vpi_get_value(vpi_handle(vpiLeftRange, select), &left);
  EXPECT_EQ(left.value.integer, 5);

  vpiHandle cat = Named(vpiFsm, By("top"), "cat_fsm");
  ASSERT_NE(cat, nullptr);
  vpiHandle concat = vpi_handle(vpiFsmStateExpression, cat);
  EXPECT_EQ(OpOf(concat), vpiConcatOp);
  std::vector<std::string> operands;
  for (vpiHandle operand : OperandsOf(concat)) {
    operands.emplace_back(vpi_get_str(vpiName, operand));
  }
  EXPECT_EQ(operands, (std::vector<std::string>{"hi", "lo"}));
}

TEST_F(ItemCoverageRun, AnFsmReachesItsStates) {
  Run(kFsmDesign);
  vpiHandle fsm = Named(vpiFsm, By("top"), "st");
  ASSERT_NE(fsm, nullptr);
  EXPECT_EQ(NamesOf(vpiFsmStates, fsm),
            (std::vector<std::string>{"DONE", "IDLE", "RUN"}));
  EXPECT_EQ(KindsOf(vpiFsmStates, fsm),
            (std::vector<int>{vpiFsmHandle, vpiFsmHandle, vpiFsmHandle}));
}

TEST_F(ItemCoverageRun, AStateHandleHoldsItsParameterValue) {
  Run(kFsmDesign);
  vpiHandle fsm = Named(vpiFsm, By("top"), "st");
  ASSERT_NE(fsm, nullptr);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(Named(vpiFsmStates, fsm, "DONE"), &value);
  EXPECT_EQ(value.value.integer, 2);
}

TEST_F(ItemCoverageRun, FsmAndStateHandlesReadTheStatesReached) {
  Run(kFsmDesign);
  vpiHandle fsm = Named(vpiFsm, By("top"), "st");
  ASSERT_NE(fsm, nullptr);
  EXPECT_EQ(vpi_get(vpiCoveredMax, fsm), 3);
  EXPECT_EQ(vpi_get(vpiCovered, fsm), 2);
  EXPECT_EQ(vpi_get(vpiCoveredCount, fsm), 3);

  vpiHandle idle = Named(vpiFsmStates, fsm, "IDLE");
  vpiHandle done = Named(vpiFsmStates, fsm, "DONE");
  EXPECT_EQ(vpi_get(vpiCoveredMax, idle), 1);
  EXPECT_EQ(vpi_get(vpiCovered, idle), 1);
  EXPECT_EQ(vpi_get(vpiCoveredCount, idle), 2);
  EXPECT_EQ(vpi_get(vpiCoveredMax, done), 1);
  EXPECT_EQ(vpi_get(vpiCovered, done), 0);
}

TEST_F(ItemCoverageRun, OnlyItemHandlesAnswerItemCoverage) {
  Run(kFsmDesign);
  vpiHandle fsm = Named(vpiFsm, By("top"), "st");
  ASSERT_NE(fsm, nullptr);
  EXPECT_EQ(vpi_get(vpiAssertAttemptCovered, fsm), 0);
  EXPECT_EQ(vpi_get(vpiCovered, By("top")), 0);
  EXPECT_EQ(vpi_handle(vpiFsmStateExpression, By("top")), nullptr);
}

}  // namespace
}  // namespace delta
