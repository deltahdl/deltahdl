// Tests for IEEE 1800-2023 §40.5.2 "Obtaining coverage information".
//
// This subclause has no grammar; it describes what a PLI client reads back
// through vpi_get() for the coverage properties of §40.5.1. Each test observes
// a production helper deriving a reported coverage figure from raw simulator
// tallies, mirroring the corresponding vpi_get() property.

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

// C5: vpiAssertSuccessCovered reports nonvacuous successes, or, for a cover
// sequence handle, the number of matches.
TEST(CoverageInformationQueries, SuccessCoveredReportsNonvacuousSuccesses) {
  AssertionCoverageCounters c;
  c.successes = 4;
  EXPECT_EQ(AssertSuccessCovered(c), 4U);

  AssertionCoverageCounters seq;
  seq.is_cover_sequence = true;
  seq.successes = 9;  // matches of the cover sequence
  EXPECT_EQ(AssertSuccessCovered(seq), 9U);
}

// C1 + C4-C9: the dispatch from a §40.5.1 assertion-status property to its
// reported count returns the right tally for each property and 0 for a
// non-assertion-status property.
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
  // A property that is not an assertion-status count contributes nothing.
  EXPECT_EQ(AssertionStatusQuery(CoverageProperty::kStatementCoverage, c), 0U);
}

// C3: vpiCovered on an assertion is true only when the assertion has been
// attempted, has succeeded nonvacuously, and has never failed.
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

// C3 (edge): only nonvacuous successes count toward coverage. An assertion that
// has been attempted and has only ever succeeded vacuously is not covered.
TEST(CoverageInformationQueries, AssertionCoveredExcludesVacuousOnlySuccess) {
  AssertionCoverageCounters vacuous_only;
  vacuous_only.attempts = 4;
  vacuous_only.vacuous_successes = 4;
  EXPECT_FALSE(AssertionCovered(vacuous_only));
}

// C12: Table 40-3 worked example for anvr, aundf, afail, apass.
TEST(CoverageInformationQueries, WorkedExampleAssertionCoverageResults) {
  // anvr: never attempted.
  AssertionCoverageCounters anvr;
  EXPECT_FALSE(AssertionCovered(anvr));
  EXPECT_EQ(AssertAttemptCovered(anvr), 0U);
  EXPECT_EQ(AssertSuccessCovered(anvr), 0U);
  EXPECT_EQ(AssertFailureCovered(anvr), 0U);

  // aundf: attempted but never passes or fails.
  AssertionCoverageCounters aundf;
  aundf.attempts = 5;
  EXPECT_FALSE(AssertionCovered(aundf));
  EXPECT_GT(AssertAttemptCovered(aundf), 0U);
  EXPECT_EQ(AssertSuccessCovered(aundf), 0U);
  EXPECT_EQ(AssertFailureCovered(aundf), 0U);

  // afail: attempted, fails.
  AssertionCoverageCounters afail;
  afail.attempts = 5;
  afail.failures = 5;
  EXPECT_FALSE(AssertionCovered(afail));
  EXPECT_GT(AssertAttemptCovered(afail), 0U);
  EXPECT_EQ(AssertSuccessCovered(afail), 0U);
  EXPECT_GT(AssertFailureCovered(afail), 0U);

  // apass: attempted, succeeds on each attempt.
  AssertionCoverageCounters apass;
  apass.attempts = 5;
  apass.successes = 5;
  EXPECT_TRUE(AssertionCovered(apass));
  EXPECT_GT(AssertAttemptCovered(apass), 0U);
  EXPECT_GT(AssertSuccessCovered(apass), 0U);
  EXPECT_EQ(AssertFailureCovered(apass), 0U);
}

// C10: in-progress attempts derive from attempts minus all concluded outcomes.
TEST(CoverageInformationQueries,
     InProgressDerivesFromAttemptsMinusConclusions) {
  AssertionCoverageCounters c;
  c.attempts = 10;
  c.successes = 3;
  c.vacuous_successes = 1;
  c.disabled = 1;
  c.killed = 1;
  c.failures = 2;
  // 10 - (3 + 1 + 1 + 1 + 2) = 2 still in progress.
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

// C10 (edge): the derivation never reports a negative figure. Should the
// recorded outcomes ever exceed the attempt count the in-progress total is
// clamped to zero rather than wrapping around.
TEST(CoverageInformationQueries, InProgressClampsWhenOutcomesExceedAttempts) {
  AssertionCoverageCounters c;
  c.attempts = 2;
  c.successes = 3;  // more recorded conclusions than counted attempts
  c.failures = 2;
  const std::optional<std::uint64_t> kInProgress = AssertInProgress(c);
  ASSERT_TRUE(kInProgress.has_value());
  if (!kInProgress.has_value()) return;
  EXPECT_EQ(kInProgress.value(), 0U);
}

// C11: the in-progress identity does not apply to cover sequences.
TEST(CoverageInformationQueries, InProgressUndefinedForCoverSequence) {
  AssertionCoverageCounters seq;
  seq.is_cover_sequence = true;
  seq.attempts = 3;
  seq.successes = 7;  // more matches than attempts is legitimate here
  EXPECT_FALSE(AssertInProgress(seq).has_value());
}

// C2: vpiCovered on a multi-entity handle reports how many entities are covered
// (statements, FSM states, or individual signal bits).
TEST(CoverageInformationQueries, CoveredEntityCountReportsCoveredEntities) {
  EntityCoverage e;
  e.total = 8;
  e.covered = 5;
  EXPECT_EQ(CoveredEntityCount(e), 5U);
}

// C13: vpiCoveredCount reports how many times an item has been covered.
TEST(CoverageInformationQueries, CoveredCountReportsHitCount) {
  EntityCoverage e;
  e.total = 8;
  e.covered = 5;
  e.hit_count = 42;
  EXPECT_EQ(CoveredCount(e), 42U);
}

// C14: vpiCoveredMax reports the number of coverable entities a handle points
// to. For an aggregate handle (statement block, signal, or FSM) that is the
// entity total.
TEST(CoverageInformationQueries, CoveredMaxReportsEntityTotalForAggregate) {
  EntityCoverage e;
  e.total = 8;
  e.covered = 5;
  EXPECT_EQ(CoveredMax(CoverageHandleKind::kAggregate, e), 8U);
}

// C14 ('shall'): vpiCoveredMax shall always be 1 for an assertion handle or an
// FSM state handle, even when the underlying tally happens to report a larger
// entity total. Such a handle denotes exactly one coverable entity.
TEST(CoverageInformationQueries, CoveredMaxIsOneForAssertionAndFsmStateHandle) {
  EntityCoverage e;
  e.total = 8;  // a stray total must not leak through for these handle kinds
  e.covered = 5;
  EXPECT_EQ(CoveredMax(CoverageHandleKind::kAssertion, e), 1U);
  EXPECT_EQ(CoveredMax(CoverageHandleKind::kFsmState, e), 1U);
}

// C1: vpi_get(<coverageType>, instance_handle) selects the covered-item count
// for the requested coverage type within the instance.
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
  // A property that is not a coverage type selects nothing.
  EXPECT_EQ(InstanceCoverageCount(CoverageProperty::kCovered, inst), 0U);
}

// A design run with its VPI model built, whose coverable items are read back
// through vpi_get() once the run is over.
using ItemCoverageRun = VpiDesignRun;

// An FSM of three legal states, entering IDLE twice and RUN once and never
// reaching DONE.
constexpr const char* kFsmDesign =
    "module top;\n"
    "  parameter [1:0] /* tool enum fsm_e */ IDLE = 0, RUN = 1, DONE = 2;\n"
    "  /* tool state_vector st enum fsm_e */\n"
    "  logic [1:0] st;\n"
    "  initial begin\n"
    "    st = IDLE; #1 st = RUN; #1 st = IDLE;\n"
    "  end\n"
    "endmodule\n";

// §40.5.2 on an assertion handle: an assertion that held at every attempt is
// covered, its successes counted, one that failed at every attempt is not,
// its failures counted, and one whose clock never ticked has no tally at all;
// one whose antecedent never held succeeded vacuously at every attempt, which
// covers nothing; each is one coverable entity (#7532).
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

// §40.5.2 on a statement handle: a block stands for the statements it holds,
// the then branch among them, which never ran; any other statement stands for
// itself and the statements it holds (#7533).
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

// §40.5.2 on a statement handle: a fork, as a block does, stands for the
// statements it holds, both of which ran.
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

// §40.5.2 on a signal handle: a signal stands for its bits, a bit covered once
// it has held both values, and its covered count is the toggles of its bits
// summed - bit 0 moved once and bit 1 twice (#7534).
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

// §40.5.2 on a port's handle: a port is a signal of its instance and stands
// for its bits. An inout port is one net with its connection, which each
// instance holding it still counts on its own (#7542).
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

// §40.5.2: a signal's bits are counted as its own, so a bit of a variable or
// of a net is no item of its own and answers no coverage, while the signal
// holding it does.
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

// §40.5.2: vpi_iterate(vpiFsm, instance) reaches the FSMs of the instance,
// each named by its state signal where no fsm_name is written (#7535).
TEST_F(ItemCoverageRun, AnInstanceReachesItsFsms) {
  Run(kFsmDesign);
  EXPECT_EQ(NamesOf(vpiFsm, By("top")), std::vector<std::string>{"st"});
  EXPECT_EQ(KindsOf(vpiFsm, By("top")), std::vector<int>{vpiFsm});
}

// A module declaring an FSM of two legal states, for instances below the top.
constexpr const char* kLeafFsm =
    "module leaf;\n"
    "  parameter [1:0] /* tool enum fsm_e */ IDLE = 0, RUN = 1;\n"
    "  /* tool state_vector st enum fsm_e */\n"
    "  logic [1:0] st;\n"
    "endmodule\n";

// §40.5.2: an instance below the top reaches the FSMs its module declares
// just as the top does.
TEST_F(ItemCoverageRun, AnInstanceBelowTheTopReachesItsFsms) {
  Run(std::string(kLeafFsm) +
      "module top;\n"
      "  leaf u();\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiFsm, By("top.u")), std::vector<std::string>{"st"});
}

// §40.5.2 with §27.5: an instance a generate block holds reaches its FSMs as
// well, each reaching the signal of that instance holding its state and its
// legal states (#7543).
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

// §40.5.2: vpi_handle(vpiFsmStateExpression, fsm) reaches the signal holding
// the FSM's state; where a part-select holds it, that part-select of the
// signal with the bounds the pragma wrote; and where several signals do, their
// concatenation, the signals its operands in the order written (#7536).
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

// §40.5.2: vpi_iterate(vpiFsmStates, fsm) reaches the FSM's legal states, of
// the second FSM handle type §40.5.1 names (#7537).
TEST_F(ItemCoverageRun, AnFsmReachesItsStates) {
  Run(kFsmDesign);
  vpiHandle fsm = Named(vpiFsm, By("top"), "st");
  ASSERT_NE(fsm, nullptr);
  EXPECT_EQ(NamesOf(vpiFsmStates, fsm),
            (std::vector<std::string>{"DONE", "IDLE", "RUN"}));
  EXPECT_EQ(KindsOf(vpiFsmStates, fsm),
            (std::vector<int>{vpiFsmHandle, vpiFsmHandle, vpiFsmHandle}));
}

// §40.5.2: vpi_get_value() on an FSM state handle reads the value of the
// state's parameter (#7538).
TEST_F(ItemCoverageRun, AStateHandleHoldsItsParameterValue) {
  Run(kFsmDesign);
  vpiHandle fsm = Named(vpiFsm, By("top"), "st");
  ASSERT_NE(fsm, nullptr);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(Named(vpiFsmStates, fsm, "DONE"), &value);
  EXPECT_EQ(value.value.integer, 2);
}

// §40.5.2 on FSM handles: an FSM stands for its states, two of the three
// reached and entered three times in all; a state is one entity, reached or
// not, its count the times the FSM entered it (#7539).
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

// §40.5.2: the assertion-specific properties are an assertion handle's alone,
// and an instance handle is no single coverable item, so neither an FSM's nor
// the instance's answers through them; vpi_get() falls back to 0, and an
// instance, holding no state, reaches no state expression (#7539).
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
