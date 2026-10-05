#include <gtest/gtest.h>

#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.60 Atomic statement: the object model diagram groups the procedural
// statement kinds under the "atomic stmt" class and gives them one label access
// edge - "-> label", str: vpiName. The clause's sole numbered Detail governs
// that edge: vpiName reports the statement's label when one was written, and
// NULL otherwise. These tests observe the production code that classifies the
// grouping (VpiIsAtomicStmtType) and applies the label rule through the public
// vpi_get_str(vpiName) dispatch path.

// The fixture installs a context so the public vpi_get_str entry point runs its
// real dispatch over the test objects.
class AtomicStatement : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// The grouping: every statement kind drawn inside the atomic stmt class - the
// concrete members standing in for the waits, disables, and tf call groupings -
// is recognized as a member.
TEST_F(AtomicStatement, DiagramMembersAreAtomicStatements) {
  for (int type : {vpiIf,
                   vpiIfElse,
                   vpiWhile,
                   vpiRepeat,
                   vpiWait,
                   vpiCase,
                   vpiFor,
                   vpiDelayControl,
                   vpiEventControl,
                   vpiEventStmt,
                   vpiAssignment,
                   vpiAssignStmt,
                   vpiDeassign,
                   vpiDisable,
                   vpiTaskCall,
                   vpiSysTaskCall,
                   vpiMethodTaskCall,
                   vpiForever,
                   vpiForce,
                   vpiRelease,
                   vpiDoWhile,
                   vpiExpectStmt,
                   vpiForeachStmt,
                   vpiImmediateAssert,
                   vpiImmediateAssume,
                   vpiImmediateCover,
                   vpiReturnStmt,
                   vpiBreak,
                   vpiContinue,
                   vpiNullStmt}) {
    EXPECT_TRUE(VpiIsAtomicStmtType(type)) << "type constant " << type;
  }
}

// Object kinds outside the atomic stmt grouping are not classified as members -
// including a sequential block (vpiBegin), which is a statement container
// rather than an atomic statement.
TEST_F(AtomicStatement, NonStatementKindsAreNotAtomicStatements) {
  EXPECT_FALSE(VpiIsAtomicStmtType(vpiModule));
  EXPECT_FALSE(VpiIsAtomicStmtType(vpiNet));
  EXPECT_FALSE(VpiIsAtomicStmtType(vpiConstant));
  EXPECT_FALSE(VpiIsAtomicStmtType(vpiBegin));
}

// D1: when the statement was written with a label, vpiName reports that label.
TEST_F(AtomicStatement, LabeledStatementReportsItsLabel) {
  VpiObject stmt;
  stmt.type = vpiIf;
  stmt.name = "check_it";  // the statement label
  EXPECT_STREQ(vpi_get_str(vpiName, VpiHandleOf(&stmt)), "check_it");
}

// D1: when no label was given, vpiName is NULL rather than the empty string -
// covering both an unset name and a label recorded as an empty string, since
// the production code treats either as "no label". This is the outcome that
// distinguishes the clause's rule, applied by the production code, from simply
// handing back the stored name pointer.
TEST_F(AtomicStatement, EmptyLabelIsTreatedAsNoLabel) {
  VpiObject stmt;
  stmt.type = vpiWhile;
  stmt.name = "";  // explicitly empty
  EXPECT_EQ(vpi_get_str(vpiName, VpiHandleOf(&stmt)), nullptr);
}

// D1 scope guard: the empty-label-becomes-NULL conversion is specific to atomic
// statements. An object outside the grouping keeps the generic name behavior,
// so an empty name comes back as the empty string rather than NULL. This pins
// the production guard (VpiIsAtomicStmtType) to the atomic statement case -
// without it, the rule would wrongly nullify empty names for every object kind.
TEST_F(AtomicStatement, EmptyNameNullingDoesNotApplyToNonAtomicObjects) {
  VpiObject non_stmt;
  non_stmt.type = vpiModule;  // not an atomic statement
  non_stmt.name = "";         // empty, same as the unlabeled case above
  const char* result = vpi_get_str(vpiName, VpiHandleOf(&non_stmt));
  ASSERT_NE(result, nullptr);
  EXPECT_STREQ(result, "");
}

// §37.60 draws twenty-eight members inside the atomic stmt class, and drawing
// them separately is a claim that they are separate: a vpi_get(vpiType) on a
// statement reports one of them, and two members sharing a constant leave that
// report unable to say which one it found. Annex M is what numbers them, and it
// gives an immediate assume 694 and an immediate cover 695 -- the 666 and 667
// they carried are vpiReturn's and vpiAnyPattern's, so an immediate assume read
// as a return statement and an immediate cover as a case-item any-pattern.
TEST_F(AtomicStatement, TheMembersOfTheClassHaveConstantsOfTheirOwn) {
  EXPECT_EQ(vpiImmediateAssert, 665);
  EXPECT_EQ(vpiImmediateAssume, 694);
  EXPECT_EQ(vpiImmediateCover, 695);
  EXPECT_EQ(vpiReturnStmt, 691);

  // The three the collisions were with, which the class draws elsewhere or not
  // at all: a return statement is its own member, while vpiReturn and
  // vpiAnyPattern are not statements.
  EXPECT_NE(vpiImmediateAssume, vpiReturn);
  EXPECT_NE(vpiImmediateCover, vpiAnyPattern);
  EXPECT_NE(vpiImmediateAssume, vpiReturnStmt);
}

// The tf call class drawn inside atomic stmt holds the three function call
// kinds as well as the task calls (§37.42), and §37.59 draws the same three in
// expr: a function call is an atomic statement where it was written as one and
// an expression everywhere else (#5034).
TEST_F(AtomicStatement, AFunctionCallWrittenAsAStatementIsOne) {
  for (int type : {vpiFuncCall, vpiMethodFuncCall, vpiSysFuncCall}) {
    VpiObject call;
    call.type = type;
    EXPECT_FALSE(VpiIsAtomicStmtObject(&call)) << type;
    EXPECT_TRUE(VpiIsExprObject(&call)) << type;
    call.written_as_stmt = true;
    EXPECT_TRUE(VpiIsAtomicStmtObject(&call)) << type;
    EXPECT_FALSE(VpiIsExprObject(&call)) << type;
  }
}

// So a loop whose body is a call statement and whose condition is a call
// reaches each through its own relation, the body standing first here as a
// do-while writes it.
TEST_F(AtomicStatement, ALoopTellsItsConditionCallFromItsBodyCall) {
  VpiObject condition;
  condition.type = vpiFuncCall;
  VpiObject body;
  body.type = vpiFuncCall;
  body.written_as_stmt = true;
  VpiObject loop;
  loop.type = vpiDoWhile;
  loop.children = {&body, &condition};
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&loop))),
            &condition);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&loop))), &body);
}

// An if-else whose condition and both branches are calls reaches its else
// branch as the second of the two call statements.
TEST_F(AtomicStatement, AnIfElseReachesAnElseCallStatement) {
  VpiObject condition;
  condition.type = vpiSysFuncCall;
  VpiObject then_call;
  then_call.type = vpiFuncCall;
  then_call.written_as_stmt = true;
  VpiObject else_call;
  else_call.type = vpiMethodFuncCall;
  else_call.written_as_stmt = true;
  VpiObject branch;
  branch.type = vpiIfElse;
  branch.children = {&condition, &then_call, &else_call};
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&branch))),
            &condition);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&branch))), &then_call);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiElseStmt, VpiHandleOf(&branch))),
            &else_call);
}

// A case item's match expressions are its calls that are expressions, the
// call statement it branches to being none of them.
TEST_F(AtomicStatement, ACaseItemsCallStatementIsNoMatchExpression) {
  VpiObject match;
  match.type = vpiFuncCall;
  VpiObject action;
  action.type = vpiFuncCall;
  action.written_as_stmt = true;
  VpiObject item;
  item.type = vpiCaseItem;
  item.children = {&match, &action};
  vpiHandle it = vpi_iterate(vpiExpr, VpiHandleOf(&item));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &match);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

// -----------------------------------------------------------------------------
// The atomic statements of a run, built from the elaborated design rather than
// by hand.
// -----------------------------------------------------------------------------

class AtomicStatementsOfARun : public VpiDesignRun {
 protected:
  // The first object of `type` `ref` reaches, null for none.
  static vpiHandle First(int type, vpiHandle ref) {
    vpiHandle it = vpi_iterate(type, ref);
    return it == nullptr ? nullptr : vpi_scan(it);
  }
};

// The label property: a labeled statement reports its label through vpiName.
TEST_F(AtomicStatementsOfARun, ALabeledStatementReportsItsLabel) {
  Run("module top; event e; initial trig: -> e; endmodule\n");
  vpiHandle stmt = First(vpiEventStmt, By("top.trig"));
  ASSERT_NE(stmt, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, stmt), "trig");
}

// An unlabeled statement has no label to report.
TEST_F(AtomicStatementsOfARun, AnUnlabeledStatementReportsNoLabel) {
  Run("module top; event e; initial -> e; endmodule\n");
  vpiHandle stmt = First(vpiEventStmt, By("top"));
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(vpi_get_str(vpiName, stmt), nullptr);
}

// A null statement is an object of the run, the body of the procedure that
// writes it.
TEST_F(AtomicStatementsOfARun, ANullStatementIsAnObjectOfTheRun) {
  Run("module top; initial ; endmodule\n");
  vpiHandle proc = First(vpiProcess, By("top"));
  ASSERT_NE(proc, nullptr);
  vpiHandle body = vpi_handle(vpiStmt, proc);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(vpi_get(vpiType, body), vpiNullStmt);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiProcess, body)), VpiObjectOf(proc));
}

// A break and a continue are objects of the run, standing in the block or the
// if statement that holds them and running in the procedure.
TEST_F(AtomicStatementsOfARun, ABreakAndAContinueAreObjectsOfTheRun) {
  Run("module top; initial for (int i = 0; i < 2; i++) begin : lp\n"
      "  if (i == 0) continue;\n"
      "  break;\n"
      "end endmodule\n");
  vpiHandle lp = By("top.lp");
  ASSERT_NE(lp, nullptr);
  vpiHandle branch = First(vpiIf, lp);
  ASSERT_NE(branch, nullptr);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiStmt, branch)), vpiContinue);
  EXPECT_EQ(KindsOf(vpiBreak, lp), std::vector<int>{vpiBreak});
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiProcess, First(vpiBreak, lp))),
            VpiObjectOf(First(vpiProcess, By("top"))));
}

}  // namespace
}  // namespace delta
