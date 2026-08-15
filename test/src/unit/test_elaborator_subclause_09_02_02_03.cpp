#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AlwaysLatchElaboration, TimingControlInAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch #5 if (en) q = d;\n"
      "endmodule\n",
      f);
  // The delay is reported under §9.2.2.3. §9.2.2.2.2 states the rule for
  // always_comb and never mentions always_latch, and §9.2.2.3 is the sentence
  // that applies §9.2.2.2's statements to always_latch.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_latch shall not contain timing controls", 3,
                            "9.2.2.3"));
}

TEST(AlwaysLatchElaboration, ForkJoinInAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q;\n"
      "  always_latch begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  // The fork-join is reported under §9.2.2.3. §9.2.2.2.2 states the rule for
  // always_comb and never mentions always_latch, and §9.2.2.3 is the sentence
  // that applies §9.2.2.2's statements to always_latch.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "always_latch shall not contain fork-join statements", 3, "9.2.2.3"));
}

TEST(AlwaysLatchElaboration, IncompleteIfNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch\n"
      "    if (en) q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(AlwaysLatchElaboration, CompleteIfElseWarnsNotLatched) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q;\n"
      "  always_latch\n"
      "    if (en) q = a;\n"
      "    else q = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(AlwaysLatchElaboration, CaseWithoutDefaultNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic q;\n"
      "  always_latch\n"
      "    case (sel)\n"
      "      2'b00: q = 0;\n"
      "      2'b01: q = 1;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(AlwaysLatchElaboration, CaseWithDefaultWarnsNotLatched) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic q;\n"
      "  always_latch\n"
      "    case (sel)\n"
      "      2'b00: q = 0;\n"
      "      2'b01: q = 1;\n"
      "      default: q = 0;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(AlwaysLatchElaboration, AlwaysLatchElaboratesToCorrectKind) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch\n"
      "    if (en) q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  bool found = false;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kAlwaysLatch) found = true;
  }
  EXPECT_TRUE(found);
}

TEST(AlwaysLatchElaboration, MultiDriverTwoAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q;\n"
      "  always_latch if (en) q = a;\n"
      "  always_latch if (en) q = b;\n"
      "endmodule\n",
      f);
  // The single-driver rule §9.2.2.3 inherits is reported under §9.2.2.2, at the
  // second of the two blocks.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'q' driven by multiple", 4, "9.2.2.2"));
}

TEST(AlwaysLatchElaboration, AlwaysLatchInfersSensitivityFromBody) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch if (en) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_FALSE(mod->processes[0].sensitivity.empty());
}

TEST(AlwaysLatchElaboration, EventControlInAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, d, q, clk;\n"
      "  always_latch @(posedge clk) if (en) q = d;\n"
      "endmodule\n",
      f);
  // The explicit event control is reported under §9.2.2.3. §9.2.2.2.2 states
  // the rule for always_comb and never mentions always_latch, and §9.2.2.3 is
  // the sentence that applies §9.2.2.2's statements to always_latch.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "always_latch shall not have an explicit event control", 3, "9.2.2.3"));
}

TEST(AlwaysLatchElaboration, UnconditionalAssignWarnsNotLatched) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic d, q;\n"
      "  always_latch q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(AlwaysLatchElaboration, IfElseIfElseChainWarnsNotLatched) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, d1, d2, d3, q;\n"
      "  always_latch\n"
      "    if (a) q = d1;\n"
      "    else if (b) q = d2;\n"
      "    else q = d3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(AlwaysLatchElaboration, TwoAlwaysLatchDifferentSignalsNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q1, q2;\n"
      "  always_latch if (en) q1 = a;\n"
      "  always_latch if (en) q2 = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.2.2.3 inherits §9.2.2.2's single-driver rule, which also forbids an
// always_latch output from being driven by a continuous assignment. This
// exercises the process-vs-continuous-assign conflict path, distinct from the
// process-vs-process path covered above.
TEST(AlwaysLatchElaboration, ContinuousAssignAndAlwaysLatchSameVarErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q;\n"
      "  assign q = b;\n"
      "  always_latch if (en) q = a;\n"
      "endmodule\n",
      f);
  // The process-versus-continuous-assignment conflict is reported under
  // §10.3.2, at the always_latch, rather than under §9.2.2.2.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'q' driven by always_latch and continuous assignment", 4,
      "10.3.2"));
}

// §9.2.2.3 inherits §9.2.2.2's statement restrictions; a blocking wait control
// is not permitted in an always_latch body.
TEST(AlwaysLatchElaboration, WaitStatementInAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch begin\n"
      "    wait (en) q = d;\n"
      "  end\n"
      "endmodule\n",
      f);
  // A wait is one of the blocking statements §9.2.2.2.2 forbids in an
  // always_comb, and §9.2.2.3 is what applies that statement to always_latch,
  // so the report stands under §9.2.2.3.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_latch shall not contain timing controls", 3,
                            "9.2.2.3"));
}

// §9.2.2.3 states that §9.2.2.2's rules apply to always_latch. §9.2.2.2's
// single-driver rule forbids an always_latch output from also being assigned by
// any other process, including a general-purpose always block.
TEST(AlwaysLatchElaboration, AlwaysLatchAndGeneralAlwaysSameVarErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q;\n"
      "  always_latch if (en) q = a;\n"
      "  always @(b) q = b;\n"
      "endmodule\n",
      f);
  // The report stands at the always_latch, under the §9.2.2.2 rule §9.2.2.3
  // adopts.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'q' driven by always_latch and another process", 3, "9.2.2.2"));
}

// The "any other process" in §9.2.2.2's single-driver rule, applied to
// always_latch via §9.2.2.3, also covers an initial block driving the same
// variable.
TEST(AlwaysLatchElaboration, AlwaysLatchAndInitialSameVarErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, a, q;\n"
      "  initial q = 0;\n"
      "  always_latch if (en) q = a;\n"
      "endmodule\n",
      f);
  // The report stands at the always_latch, under the §9.2.2.2 rule §9.2.2.3
  // adopts.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'q' driven by always_latch and another process", 4, "9.2.2.2"));
}

// The single-driver conflict is keyed on overlapping targets: an always_latch
// and a general always block driving distinct variables coexist without error.
TEST(AlwaysLatchElaboration, AlwaysLatchAndGeneralAlwaysDifferentVarsNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q1, q2;\n"
      "  always_latch if (en) q1 = a;\n"
      "  always @(b) q2 = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The latch-inference check recurses into begin-end blocks: an incomplete if
// nested inside a block still infers a latch, so no "does not represent latched
// logic" warning is raised.
TEST(AlwaysLatchElaboration, BlockWrappingIncompleteIfNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch begin\n"
      "    if (en) q = d;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §9.2.2.3 applies §9.2.2.2's single-driver rule to always_latch. The forbidden
// "other process" also includes an always_comb procedure driving the same
// variable, a distinct process form from the latch/continuous/general cases.
TEST(AlwaysLatchElaboration, MultiDriverAlwaysLatchAndAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q;\n"
      "  always_comb q = a;\n"
      "  always_latch if (en) q = b;\n"
      "endmodule\n",
      f);
  // The report stands at the second of the two processes, under §9.2.2.2.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'q' driven by multiple", 4, "9.2.2.2"));
}

// §9.2.2.2's single-driver rule is stated per term of the longest static prefix
// (§11.5.3), so distinct elements of an unpacked array are independent driver
// targets. Built from real array-element syntax and driven through elaboration,
// this shows the rule — as applied to always_latch by §9.2.2.3 — treating two
// literal-indexed elements as non-overlapping.
TEST(AlwaysLatchElaboration, TwoAlwaysLatchIndependentArrayElementsNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  logic [7:0] arr [0:1];\n"
      "  always_latch if (en) arr[0] = 8'd1;\n"
      "  always_latch if (en) arr[1] = 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The negative form of the element-granular single-driver rule: two
// always_latch procedures writing the same literal-indexed element overlap and
// are rejected.
TEST(AlwaysLatchElaboration, TwoAlwaysLatchSameArrayElementErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  logic [7:0] arr [0:1];\n"
      "  always_latch if (en) arr[0] = 8'd1;\n"
      "  always_latch if (en) arr[0] = 8'd2;\n"
      "endmodule\n",
      f);
  // The overlapping target is named by its longest static prefix (§11.5.3), and
  // the report stands at the second block under §9.2.2.2.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'arr[0]' driven by multiple", 5,
                            "9.2.2.2"));
}

// §9.2.2.3 asks a tool to "warn if the behavior in an always_latch construct
// does not represent latched logic". The subject is the behavior, so an
// incomplete if is not the question by itself. Here the if narrows a value `q`
// has already been given on this pass, so every path leaves `q` holding
// something computed from `d` and `e` and nothing is carried over. There is no
// latch to model, and the warning says so.
TEST(AlwaysLatchElaboration,
     UnconditionalAssignBeforeIncompleteIfWarnsNoLatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, d, e, q;\n"
      "  always_latch begin\n"
      "    q = d;\n"
      "    if (en) q = e;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// The other direction, and the reason the check cannot be a rule about whether
// an `else` branch is present. Both arms of this if are written, so nothing is
// missing from the shape of the control flow, but `r` is assigned in one arm
// only: when `en` is false, `r` keeps the value it held. That is a latch, so
// the procedure models what always_latch says it models and nothing is warned.
TEST(AlwaysLatchElaboration, CompleteIfElseLeavingOneOutputHeldNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, d, e, f2, q, r;\n"
      "  always_latch\n"
      "    if (en) begin\n"
      "      q = d;\n"
      "      r = e;\n"
      "    end else begin\n"
      "      q = f2;\n"
      "    end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §11.5.3 keeps an indexed select inside the longest static prefix only when
// the index is a constant expression (§11.2.1). A module parameter is such a
// constant, resolved via the parameter scope rather than as a literal, so two
// distinct parameter indices name distinct elements and do not conflict.
TEST(AlwaysLatchElaboration, IndependentArrayElementsParamIndexNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int P0 = 0, parameter int P1 = 1);\n"
      "  logic en;\n"
      "  logic [7:0] arr [0:1];\n"
      "  always_latch if (en) arr[P0] = 8'd1;\n"
      "  always_latch if (en) arr[P1] = 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The parameter-index negative: the same parameter folds to the same element,
// so the prefixes overlap and the two always_latch drivers are rejected. This
// exercises the constant-resolution path, distinct from the literal-index form.
TEST(AlwaysLatchElaboration, OverlappingArrayElementsParamIndexErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter int P = 0);\n"
      "  logic en;\n"
      "  logic [7:0] arr [0:1];\n"
      "  always_latch if (en) arr[P] = 8'd1;\n"
      "  always_latch if (en) arr[P] = 8'd2;\n"
      "endmodule\n",
      f);
  // The prefix names the folded index, so the report reads 'arr[0]' rather than
  // 'arr[P]', and it stands at the second block under §9.2.2.2.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'arr[0]' driven by multiple", 5,
                            "9.2.2.2"));
}

// A localparam is also a constant expression (§11.2.1) resolved through the
// parameter scope, so two distinct localparam indices name distinct array
// elements and the always_latch drivers coexist without error.
TEST(AlwaysLatchElaboration, IndependentArrayElementsLocalparamIndexNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int P0 = 0;\n"
      "  localparam int P1 = 1;\n"
      "  logic en;\n"
      "  logic [7:0] arr [0:1];\n"
      "  always_latch if (en) arr[P0] = 8'd1;\n"
      "  always_latch if (en) arr[P1] = 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.2.2.3 rules that "All statements in 9.2.2.2 shall apply to always_latch",
// and §9.2.2.2.2 is where those statements say that a statement in the
// procedure "shall not include those that block, have blocking timing or event
// controls". §14.11 has a cycle delay wait for the specified number of clocking
// block events, so `##3` blocks and an always_latch shall not contain it.
//
// The subclause asserted is the one the emission site passes, which is
// §9.2.2.3 for an always_latch and §9.2.2.2.2 for an always_comb, because
// §9.2.2.2.2 speaks only of always_comb and §9.2.2.3 is the sentence that
// applies its statements to always_latch. The line is the always_latch
// keyword's rather than the `##3`'s, since the report stands at the procedure.
// The source draws a second error, "cycle delay (##) requires a default
// clocking block" under §14.11, for having no default clocking; naming the
// message, the line and the subclause is what keeps this case answering for
// §9.2.2.3 rather than for whichever report came first.
TEST(AlwaysLatchElaboration, CycleDelayInAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic d, q;\n"
      "  always_latch begin\n"
      "    ##3 q = d;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_latch shall not contain timing controls", 3,
                            "9.2.2.3"));
}

}  // namespace
