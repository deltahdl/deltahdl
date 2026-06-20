#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

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
                   vpiForever,
                   vpiForce,
                   vpiRelease,
                   vpiDoWhile,
                   vpiExpectStmt,
                   vpiForeachStmt,
                   vpiImmediateAssert,
                   vpiImmediateAssume,
                   vpiImmediateCover,
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
  EXPECT_STREQ(vpi_get_str(vpiName, &stmt), "check_it");
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
  EXPECT_EQ(vpi_get_str(vpiName, &stmt), nullptr);
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
  const char* result = vpi_get_str(vpiName, &non_stmt);
  ASSERT_NE(result, nullptr);
  EXPECT_STREQ(result, "");
}

}  // namespace
}  // namespace delta
