#include <gtest/gtest.h>

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
  for (const auto& reported : f.diag.Diagnostics()) {
    EXPECT_EQ(reported.message.find("§"), std::string::npos);
  }
}

TEST(DeferredAssertionElaboration,
     DISABLED_FinalDeferredCalleeAssignsInAForkArmReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task mutator;\n"
      "    fork\n"
      "      x = 8'd1;\n"
      "    join\n"
      "  endtask\n"
      "  initial assert final (1) mutator();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "whose body contains statements not legally "
                            "callable in the Postponed region",
                            8, "16.4"));
}

TEST(DeferredAssertionElaboration,
     DISABLED_FinalDeferredCalleeAssignsInAForInitializationReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task mutator;\n"
      "    for (x = 8'd0; 1'b0; ) ;\n"
      "  endtask\n"
      "  initial assert final (1) mutator();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "whose body contains statements not legally "
                            "callable in the Postponed region",
                            6, "16.4"));
}

TEST(DeferredAssertionElaboration,
     DISABLED_FinalDeferredCalleeAssignsInAForStepReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task mutator;\n"
      "    for ( ; 1'b0; x = 8'd1) ;\n"
      "  endtask\n"
      "  initial assert final (1) mutator();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "whose body contains statements not legally "
                            "callable in the Postponed region",
                            6, "16.4"));
}

TEST(DeferredAssertionElaboration,
     DISABLED_FinalDeferredCalleeAssignsInAnAssertionPassActionReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task mutator;\n"
      "    assert (1'b1) x = 8'd1;\n"
      "  endtask\n"
      "  initial assert final (1) mutator();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "whose body contains statements not legally "
                            "callable in the Postponed region",
                            6, "16.4"));
}

TEST(DeferredAssertionElaboration,
     DISABLED_FinalDeferredCalleeAssignsInAnAssertionFailActionReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task mutator;\n"
      "    assert (1'b1) else x = 8'd1;\n"
      "  endtask\n"
      "  initial assert final (1) mutator();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "whose body contains statements not legally "
                            "callable in the Postponed region",
                            6, "16.4"));
}

TEST(DeferredAssertionElaboration,
     DISABLED_FinalDeferredCalleeAssignsInARandcaseArmReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task mutator;\n"
      "    randcase\n"
      "      1 : x = 8'd1;\n"
      "    endcase\n"
      "  endtask\n"
      "  initial assert final (1) mutator();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "whose body contains statements not legally "
                            "callable in the Postponed region",
                            8, "16.4"));
}

TEST(DeferredAssertionElaboration,
     DISABLED_FinalDeferredCalleeAssignsInARandsequenceCodeBlockReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task mutator;\n"
      "    randsequence(main)\n"
      "      main : { x = 8'd1; };\n"
      "    endsequence\n"
      "  endtask\n"
      "  initial assert final (1) mutator();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "whose body contains statements not legally "
                            "callable in the Postponed region",
                            8, "16.4"));
}

TEST(DeferredAssertionElaboration,
     AutomaticLocalToRefFormalInAForkArmRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  task automatic upd(ref int r); endtask\n"
      "  task automatic caller;\n"
      "    int loc;\n"
      "    fork\n"
      "      assert #0 (1) upd(loc);\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot pass automatic variable as actual for ref "
                            "formal 'r' in deferred-assertion call",
                            6, "16.4"));
}

TEST(DeferredAssertionElaboration,
     AutomaticLocalToRefFormalInARandcaseArmRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  task automatic upd(ref int r); endtask\n"
      "  task automatic caller;\n"
      "    int loc;\n"
      "    randcase\n"
      "      1 : assert #0 (1) upd(loc);\n"
      "    endcase\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot pass automatic variable as actual for ref "
                            "formal 'r' in deferred-assertion call",
                            6, "16.4"));
}

TEST(DeferredAssertionElaboration,
     AutomaticLocalToRefFormalInARandsequenceCodeBlockRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  task automatic upd(ref int r); endtask\n"
      "  task automatic caller;\n"
      "    int loc;\n"
      "    randsequence(main)\n"
      "      main : { assert #0 (1) upd(loc); };\n"
      "    endsequence\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot pass automatic variable as actual for ref "
                            "formal 'r' in deferred-assertion call",
                            6, "16.4"));
}

TEST(DeferredAssertionElaboration,
     AutomaticDeclaredInAForkArmToRefFormalRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  task automatic upd(ref int r); endtask\n"
      "  task caller;\n"
      "    fork\n"
      "      automatic int loc;\n"
      "      assert #0 (1) upd(loc);\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot pass automatic variable as actual for ref "
                            "formal 'r' in deferred-assertion call",
                            6, "16.4"));
}

TEST(DeferredAssertionElaboration,
     StaticDeclaredInAForkArmToRefFormalAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  task automatic upd(ref int r); endtask\n"
      "  task caller;\n"
      "    fork\n"
      "      int loc;\n"
      "      assert #0 (1) upd(loc);\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(DeferredAssertionElaboration,
     AutomaticDeclaredUnderARandcaseArmToRefFormalRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  task automatic upd(ref int r); endtask\n"
      "  task caller;\n"
      "    randcase\n"
      "      1 : begin\n"
      "        automatic int loc;\n"
      "        assert #0 (1) upd(loc);\n"
      "      end\n"
      "    endcase\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot pass automatic variable as actual for ref "
                            "formal 'r' in deferred-assertion call",
                            7, "16.4"));
}

TEST(DeferredAssertionElaboration,
     StaticDeclaredUnderARandcaseArmToRefFormalAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  task automatic upd(ref int r); endtask\n"
      "  task caller;\n"
      "    randcase\n"
      "      1 : begin\n"
      "        int loc;\n"
      "        assert #0 (1) upd(loc);\n"
      "      end\n"
      "    endcase\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(DeferredAssertionElaboration,
     AutomaticDeclaredInARandsequenceCodeBlockToRefFormalRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  task automatic upd(ref int r); endtask\n"
      "  task caller;\n"
      "    randsequence(main)\n"
      "      main : { automatic int loc; assert #0 (1) upd(loc); };\n"
      "    endsequence\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot pass automatic variable as actual for ref "
                            "formal 'r' in deferred-assertion call",
                            5, "16.4"));
}

TEST(DeferredAssertionElaboration,
     StaticDeclaredInARandsequenceCodeBlockToRefFormalAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  task automatic upd(ref int r); endtask\n"
      "  task caller;\n"
      "    randsequence(main)\n"
      "      main : { int loc; assert #0 (1) upd(loc); };\n"
      "    endsequence\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(DeferredAssertionElaboration, VoidCastOfAFunctionCallIsASingleCall) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  function int report(input int n); return n; endfunction\n"
      "  initial assert #0 (c) void'(report(1)); else void'(report(0));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "deferred assertion pass action shall be a single "
                             "subroutine call",
                             4, "16.4"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "deferred assertion fail action shall be a single "
                             "subroutine call",
                             4, "16.4"));
}

}  // namespace
