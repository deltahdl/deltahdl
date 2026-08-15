#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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

// §16.4: a deferred assertion action block may contain a single subroutine
// call; a void function call is one of the permitted call forms (alongside a
// task, task method, void function method, and system task), so it is accepted
// with no single-call diagnostic, just like the task and system-task forms.
TEST(DeferredAssertionElaboration, VoidFunctionCallActionAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  function void note; endfunction\n"
      "  logic c;\n"
      "  initial assert #0 (c) note();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

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

// §16.4: "The pass and fail statements in a deferred assertion's action_block,
// if present, shall each consist of a single subroutine call. ... The
// requirement of a single subroutine call implies that no begin-end block shall
// surround the pass or fail statements, as begin is itself a statement that is
// not a subroutine call." §1.5 defines shall as a mandatory requirement "from
// which no deviation is permitted", so each of the forms below is illegal
// source and elaboration rejects it rather than reporting it and carrying on.
TEST(DeferredAssertionElaboration, BeginEndPassBlockRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial assert #0 (c) begin $info(\"a\"); $info(\"b\"); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "deferred assertion pass action shall be a single "
                            "subroutine call",
                            3, "16.4"));
}

TEST(DeferredAssertionElaboration, BeginEndFailBlockRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial assert #0 (c) else begin $error(\"x\"); $error(\"y\"); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "deferred assertion fail action shall be a single "
                            "subroutine call",
                            3, "16.4"));
}

TEST(DeferredAssertionElaboration, AssignmentInPassActionRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  logic [7:0] x;\n"
      "  initial assert #0 (c) x = 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "deferred assertion pass action shall be a single "
                            "subroutine call",
                            4, "16.4"));
}

// §16.3 gives the opposite rule for a simple immediate assertion: "the fail
// statement, like the pass statement, is any legal SystemVerilog procedural
// statement". The same begin-end block that §16.4 rejects above is therefore
// legal without the #0, and this pair pins that the rejection follows the
// deferral rather than the block.
TEST(DeferredAssertionElaboration, NonDeferredBeginEndAccepted) {
  ElabFixture deferred;
  ASSERT_NE(
      Elaborate(
          "module m;\n"
          "  logic c;\n"
          "  initial assert #0 (c) begin $info(\"a\"); $info(\"b\"); end\n"
          "endmodule\n",
          deferred),
      nullptr);
  ASSERT_TRUE(ReportedError(deferred.diag.Diagnostics(),
                            "deferred assertion pass action shall be a single "
                            "subroutine call",
                            3, "16.4"));

  ElabFixture plain;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial assert(c) begin $info(\"a\"); $info(\"b\"); end\n"
      "endmodule\n",
      plain);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(plain.has_errors);
}

TEST(DeferredAssertionElaboration, DeferredAssumeBeginEndRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial assume #0 (c) begin $info(\"a\"); $info(\"b\"); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "deferred assertion pass action shall be a single "
                            "subroutine call",
                            3, "16.4"));
}

TEST(DeferredAssertionElaboration, DeferredCoverBeginEndRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial cover #0 (c) begin $info(\"a\"); $info(\"b\"); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "deferred assertion pass action shall be a single "
                            "subroutine call",
                            3, "16.4"));
}

TEST(DeferredAssertionElaboration, FinalDeferredPostponedIllegalCalleeFlagged) {
  ElabFixture deferred_final;
  ASSERT_NE(Elaborate("module m;\n"
                      "  logic [7:0] x;\n"
                      "  task mutator; x = 8'd1; endtask\n"
                      "  initial assert final (1) mutator();\n"
                      "endmodule\n",
                      deferred_final),
            nullptr);
  uint32_t final_warnings = deferred_final.diag.WarningCount();
  ASSERT_GE(final_warnings, 1u);

  ElabFixture deferred_obs;
  ASSERT_NE(Elaborate("module m;\n"
                      "  logic [7:0] x;\n"
                      "  task mutator; x = 8'd1; endtask\n"
                      "  initial assert #0 (1) mutator();\n"
                      "endmodule\n",
                      deferred_obs),
            nullptr);
  EXPECT_LT(deferred_obs.diag.WarningCount(), final_warnings);
}

TEST(DeferredAssertionElaboration, FinalDeferredPostponedSafeCalleeAccepted) {
  ElabFixture safe;
  ASSERT_NE(Elaborate("module m;\n"
                      "  task reporter; $info(\"ok\"); endtask\n"
                      "  initial assert final (1) reporter();\n"
                      "endmodule\n",
                      safe),
            nullptr);
  ElabFixture unsafe;
  ASSERT_NE(Elaborate("module m;\n"
                      "  logic [7:0] x;\n"
                      "  task mutator; x = 8'd1; endtask\n"
                      "  initial assert final (1) mutator();\n"
                      "endmodule\n",
                      unsafe),
            nullptr);
  EXPECT_LT(safe.diag.WarningCount(), unsafe.diag.WarningCount());
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot pass dynamic variable as actual for ref "
                            "formal 'r' in deferred-assertion call",
                            5, "16.4"));
}

TEST(DeferredAssertionElaboration, StaticVarToRefFormalAccepted) {
  ElabFixture f;
  // §13.5.2: pass-by-reference is illegal for a subroutine with static
  // lifetime, so the task must be automatic for the ref formal to be legal; a
  // static variable is then accepted as the ref actual.
  auto* design = Elaborate(
      "module m;\n"
      "  int s;\n"
      "  task automatic by_ref(ref int r); endtask\n"
      "  initial assert #0 (1) by_ref(s);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.4: it shall be an error to pass a dynamic variable as the actual for a
// const ref formal too, not only a plain ref formal -- the restriction is on
// the pass-by-reference direction regardless of constness. A class property
// (dynamic storage) passed to a `const ref` formal is rejected.
TEST(DeferredAssertionElaboration, ClassMemberToConstRefFormalRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  class C; int v; endclass\n"
      "  C h = new();\n"
      "  task by_cref(const ref int r); endtask\n"
      "  initial assert #0 (1) by_cref(h.v);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot pass dynamic variable as actual for ref "
                            "const formal 'r' in deferred-assertion call",
                            5, "16.4"));
}

// §16.4: it shall be an error to pass an automatic variable as the actual for a
// ref formal of a deferred-assertion action call. A local of an automatic task
// has automatic storage, so passing it by reference is rejected.
TEST(DeferredAssertionElaboration, AutomaticLocalToRefFormalRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task automatic upd(ref int r); endtask\n"
      "  task automatic caller;\n"
      "    int loc;\n"
      "    assert #0 (1) upd(loc);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot pass automatic variable as actual for ref "
                            "formal 'r' in deferred-assertion call",
                            5, "16.4"));
}

// §16.4: the automatic-variable restriction is on the variable's storage, not
// on the enclosing subroutine's lifetime. A module-level static variable passed
// by reference is accepted even from inside an automatic task, so the check
// does not over-reject.
TEST(DeferredAssertionElaboration,
     StaticVarFromAutomaticTaskToRefFormalAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  int s;\n"
      "  task automatic use_static(ref int r); endtask\n"
      "  task automatic caller;\n"
      "    assert #0 (1) use_static(s);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.4: the report that refuses an action block which is not a single
// subroutine call names the subclause stating the rule, and states it once.
// The sentence opened with "§16.4:" until the field carried it, and
// DiagEngine::Emit appends the field, so a message that still held the sign
// would print the subclause twice.
TEST(DeferredAssertionElaboration, AssignmentPassActionNames16_4) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  logic [7:0] x;\n"
      "  initial assert #0 (c) x = 8'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "deferred assertion pass action shall be a single",
                            4, "16.4"));
  EXPECT_EQ(diag->message.find("§"), std::string::npos);
}

}  // namespace
