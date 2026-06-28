#include "fixture_elaborator.h"

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

TEST(DeferredAssertionElaboration, NonDeferredBeginEndNotFlagged) {
  ElabFixture deferred;
  ASSERT_NE(
      Elaborate(
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
  EXPECT_TRUE(f.has_errors);
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

}  // namespace
