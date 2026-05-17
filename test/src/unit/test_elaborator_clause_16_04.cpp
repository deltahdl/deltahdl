#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §16.4 "Action blocks may only contain a single subroutine call." A
// task/system-task call as the pass action is the canonical legal form
// and must elaborate without raising an error.
TEST(DeferredAssertionElaboration, SingleSystemTaskPassActionAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial assert #0 (c) $info(\"ok\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.4 P8 names a *task* (alongside void function / system task) as
// one of the legal subroutine kinds. A user-task call exercises the
// kCall branch of the elaborator's single-subroutine-call gate —
// distinct AST shape from the kSystemCall branch above.
TEST(DeferredAssertionElaboration, UserTaskCallPassActionAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task do_pass; endtask\n"
      "  logic c;\n"
      "  initial assert #0 (c) do_pass();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.4 "The pass and fail statements in a deferred assertion's
// action_block, if present, shall each consist of a single subroutine
// call." A null/omitted action must still elaborate without error.
TEST(DeferredAssertionElaboration, OmittedActionsAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial begin\n"
      "    assert #0 (c);\n"
      "    cover final (c);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.4 "The requirement of a single subroutine call implies that no
// begin-end block shall surround the pass or fail statements, as begin
// is itself a statement that is not a subroutine call." A begin block
// in the pass action must be flagged.
TEST(DeferredAssertionElaboration, BeginEndPassBlockFlagged) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial assert #0 (c) begin $info(\"a\"); $info(\"b\"); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §16.4: same begin-end rule applies to the fail (else) branch.
TEST(DeferredAssertionElaboration, BeginEndFailBlockFlagged) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial assert #0 (c) else begin $error(\"x\"); $error(\"y\"); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §16.4 "Action blocks may only contain a single subroutine call." A
// blocking assignment is not a subroutine call, so the action shall be
// flagged.
TEST(DeferredAssertionElaboration, AssignmentInPassActionFlagged) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  logic [7:0] x;\n"
      "  initial assert #0 (c) x = 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §16.4: simple immediate assertions (no #0 / no final) are governed by
// §16.3 and have no single-subroutine-call restriction. A begin-end pass
// block on a non-deferred assertion must NOT raise the §16.4 warning.
// Demonstrate the gate by comparing to a sibling fixture that does have
// a deferred begin-end action: the deferred form raises a §16.4 warning,
// the non-deferred form raises strictly fewer.
TEST(DeferredAssertionElaboration, NonDeferredBeginEndNotFlagged) {
  ElabFixture deferred;
  ASSERT_NE(Elaborate(
                "module m;\n"
                "  logic c;\n"
                "  initial assert #0 (c) begin $info(\"a\"); $info(\"b\"); end\n"
                "endmodule\n",
                deferred),
            nullptr);
  uint32_t deferred_warnings = deferred.diag.WarningCount();
  ASSERT_GE(deferred_warnings, 1u);

  ElabFixture plain;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial assert(c) begin $info(\"a\"); $info(\"b\"); end\n"
      "endmodule\n",
      plain);
  ASSERT_NE(design, nullptr);
  EXPECT_LT(plain.diag.WarningCount(), deferred_warnings);
}

// §16.4: the same single-subroutine-call rule applies to deferred
// assume and cover. A begin-end pass block on `assume #0` must be
// flagged.
TEST(DeferredAssertionElaboration, DeferredAssumeBeginEndFlagged) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial assume #0 (c) begin $info(\"a\"); $info(\"b\"); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(DeferredAssertionElaboration, DeferredCoverBeginEndFlagged) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial cover #0 (c) begin $info(\"a\"); $info(\"b\"); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §16.4 P10: "In the case of a final deferred assertion, the subroutine
// shall be one that may be legally called in the Postponed region (see
// 4.4.2.9)." A user task whose body performs a blocking assign violates
// §4.4.2.9's no-value-change rule, so a final-deferred call to it must
// be flagged. The same call from an observed deferred form is not
// constrained by P10 — only the final form is — confirming the gate
// fires only for is_final_deferred.
TEST(DeferredAssertionElaboration, FinalDeferredPostponedIllegalCalleeFlagged) {
  ElabFixture deferred_final;
  ASSERT_NE(Elaborate(
                "module m;\n"
                "  logic [7:0] x;\n"
                "  task mutator; x = 8'd1; endtask\n"
                "  initial assert final (1) mutator();\n"
                "endmodule\n",
                deferred_final),
            nullptr);
  uint32_t final_warnings = deferred_final.diag.WarningCount();
  ASSERT_GE(final_warnings, 1u);

  ElabFixture deferred_obs;
  ASSERT_NE(Elaborate(
                "module m;\n"
                "  logic [7:0] x;\n"
                "  task mutator; x = 8'd1; endtask\n"
                "  initial assert #0 (1) mutator();\n"
                "endmodule\n",
                deferred_obs),
            nullptr);
  EXPECT_LT(deferred_obs.diag.WarningCount(), final_warnings);
}

// §16.4 P10: final-deferred call to a Postponed-safe user task (only
// system-call body) must elaborate without the P10 warning. Compare
// against the violating-task fixture above to factor out unrelated
// baseline diagnostics.
TEST(DeferredAssertionElaboration, FinalDeferredPostponedSafeCalleeAccepted) {
  ElabFixture safe;
  ASSERT_NE(Elaborate(
                "module m;\n"
                "  task reporter; $info(\"ok\"); endtask\n"
                "  initial assert final (1) reporter();\n"
                "endmodule\n",
                safe),
            nullptr);
  ElabFixture unsafe;
  ASSERT_NE(Elaborate(
                "module m;\n"
                "  logic [7:0] x;\n"
                "  task mutator; x = 8'd1; endtask\n"
                "  initial assert final (1) mutator();\n"
                "endmodule\n",
                unsafe),
            nullptr);
  EXPECT_LT(safe.diag.WarningCount(), unsafe.diag.WarningCount());
}

// §16.4 P12: "It shall be an error to pass automatic or dynamic
// variables as actuals to a ref or const ref formal." A class-property
// access (kMemberAccess on a class instance) carries dynamic-object
// lifetime, so passing it as the actual for a ref formal in a
// deferred-assertion action call shall be rejected as an error.
TEST(DeferredAssertionElaboration, ClassMemberToRefFormalRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  class C; int v; endclass\n"
      "  C h = new();\n"
      "  task by_ref(ref int r); endtask\n"
      "  initial assert #0 (1) by_ref(h.v);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §16.4 P12: a plain (static) variable passed to the same ref formal is
// legal — the rule targets automatic/dynamic actuals specifically, so a
// module-scoped variable should not raise the §16.4 P12 error.
TEST(DeferredAssertionElaboration, StaticVarToRefFormalAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  int s;\n"
      "  task by_ref(ref int r); endtask\n"
      "  initial assert #0 (1) by_ref(s);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
