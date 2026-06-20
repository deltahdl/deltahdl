#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.74 For: the object model diagram for a for statement. The clause carries
// no numbered Details, no 'shall' sentences, and no BNF - it is the diagram
// alone. The for object draws four edges: an iteration of initialization
// statements (vpiForInitStmt), an iteration of increment statements
// (vpiForIncStmt), a controlling condition expression (vpiCondition), and an
// unlabeled edge to a body statement (the generic vpiStmt relation). It also
// carries the vpiLocalVarDecls property ("has local variables"), which is owned
// by §37.12 and is not retested here.
//
// Only the vpiCondition edge needs dedicated production code: the condition's
// own type is an expression kind, not the vpiCondition relation tag, so the
// generic child walk cannot find it - exactly as for the while/repeat (§37.66)
// and if/if-else (§37.71) statements. The initialization and increment
// iterations and the body edge are statement-edge children served by the
// generic traversal and iteration. These tests observe the production paths
// applying each rule.

// The fixture installs a context so the public vpi_handle/vpi_iterate entry
// points run their real dispatch over the test objects.
class For : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Condition edge (vpiCondition -> expr): a for statement reaches its
// controlling condition through the public vpi_handle(vpiCondition, ...)
// dispatch. The scan is type-directed: among the initialization statement,
// increment statement, and body
// - all statement-edge children - it skips every non-expression child and
// returns the condition expression rather than the first child.
TEST_F(For, ForStatementReachesConditionAmongInitIncrementAndBody) {
  VpiObject init;
  init.type = vpiForInitStmt;  // an initialization statement, listed first
  VpiObject condition;
  condition.type = vpiOperation;  // the condition: an expression kind
  VpiObject increment;
  increment.type = vpiForIncStmt;  // an increment statement
  VpiObject body;
  body.type = vpiStmt;  // the body (the diagram's unlabeled edge)

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&init, &condition, &increment, &body};

  EXPECT_EQ(VpiHandleC(vpiCondition, &for_stmt), &condition);
}

// Condition edge reports no expression when the for statement has no condition
// child (a for loop written without a controlling expression): the scan finds
// no expression among the statement-edge children and returns null.
TEST_F(For, ForWithoutConditionReportsNoCondition) {
  VpiObject init;
  init.type = vpiForInitStmt;
  VpiObject increment;
  increment.type = vpiForIncStmt;
  VpiObject body;
  body.type = vpiStmt;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&init, &increment, &body};

  EXPECT_EQ(VpiHandleC(vpiCondition, &for_stmt), nullptr);
}

// Condition gating: the for-condition relation is scoped to the for statement
// kind, so it does not disturb the vpiCondition edge other objects draw. A
// non-for object carrying an expression child is left to the generic traversal,
// which matches by exact relation tag and so does not surface that expression.
TEST_F(For, ForConditionRelationIsScopedToForStatements) {
  VpiObject expr;
  expr.type = vpiOperation;

  VpiObject not_a_for;
  not_a_for.type = vpiBegin;  // not a for statement
  not_a_for.children = {&expr};

  EXPECT_EQ(VpiHandleC(vpiCondition, &not_a_for), nullptr);
}

// Initialization edge (vpiForInitStmt iteration): a for statement may carry
// more than one initialization statement (a comma list), all reached through
// the vpiForInitStmt iteration. They are statement-edge children served by the
// generic type-matched iteration, which collects them in order while skipping
// the condition, increment, and body.
TEST_F(For, ForInitializationStatementsReachedThroughVpiForInitStmt) {
  VpiObject init0;
  init0.type = vpiForInitStmt;
  VpiObject init1;
  init1.type = vpiForInitStmt;
  VpiObject condition;
  condition.type = vpiOperation;
  VpiObject increment;
  increment.type = vpiForIncStmt;
  VpiObject body;
  body.type = vpiStmt;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&init0, &condition, &init1, &increment, &body};

  VpiHandle it = ctx_.Iterate(vpiForInitStmt, &for_stmt);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(ctx_.Scan(it), &init0);
  EXPECT_EQ(ctx_.Scan(it), &init1);
  EXPECT_EQ(ctx_.Scan(it),
            nullptr);  // drains; condition/increment/body excluded
}

// Increment edge (vpiForIncStmt iteration): symmetrically, the increment
// statements of a for statement are reached through the vpiForIncStmt
// iteration, collected in order and distinct from the initialization
// statements.
TEST_F(For, ForIncrementStatementsReachedThroughVpiForIncStmt) {
  VpiObject init;
  init.type = vpiForInitStmt;
  VpiObject increment0;
  increment0.type = vpiForIncStmt;
  VpiObject increment1;
  increment1.type = vpiForIncStmt;
  VpiObject body;
  body.type = vpiStmt;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&init, &increment0, &increment1, &body};

  VpiHandle it = ctx_.Iterate(vpiForIncStmt, &for_stmt);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(ctx_.Scan(it), &increment0);
  EXPECT_EQ(ctx_.Scan(it), &increment1);
  EXPECT_EQ(ctx_.Scan(it), nullptr);  // drains; init/body excluded
}

// Body edge (the diagram's unlabeled arrow to a statement): a for statement
// reaches its body through the public vpi_handle(vpiStmt, ...) dispatch. The
// generic vpiStmt traversal is type-directed: it skips the initialization,
// condition, and increment children and returns the body statement.
TEST_F(For, ForStatementReachesBodyThroughVpiStmt) {
  VpiObject init;
  init.type = vpiForInitStmt;
  VpiObject condition;
  condition.type = vpiOperation;
  VpiObject increment;
  increment.type = vpiForIncStmt;
  VpiObject body;
  body.type = vpiStmt;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&init, &condition, &increment, &body};

  EXPECT_EQ(VpiHandleC(vpiStmt, &for_stmt), &body);
}

// Body edge edge case (no body): a for statement carrying initialization,
// condition, and increment children but no body statement reaches no body. The
// generic vpiStmt traversal finds no statement-tagged child and reports null -
// the same type-directed path that locates the body when one is present, here
// exercised on its empty outcome.
TEST_F(For, ForWithoutBodyReportsNoStatement) {
  VpiObject init;
  init.type = vpiForInitStmt;
  VpiObject condition;
  condition.type = vpiOperation;
  VpiObject increment;
  increment.type = vpiForIncStmt;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&init, &condition, &increment};

  EXPECT_EQ(VpiHandleC(vpiStmt, &for_stmt), nullptr);
}

// Initialization edge edge case (no init statements): a for statement written
// without an initialization clause has an empty vpiForInitStmt iteration. The
// generic type-matched iteration finds no init-tagged child and reports
// nothing, even though the condition and body are present and reachable through
// their own edges.
TEST_F(For, ForInitializationIterationIsEmptyWithoutInitStatements) {
  VpiObject condition;
  condition.type = vpiOperation;
  VpiObject increment;
  increment.type = vpiForIncStmt;
  VpiObject body;
  body.type = vpiStmt;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&condition, &increment, &body};

  EXPECT_EQ(ctx_.Iterate(vpiForInitStmt, &for_stmt), nullptr);
}

// Increment edge edge case (no increment statements): symmetrically, a for
// statement with no increment clause has an empty vpiForIncStmt iteration. The
// iteration surfaces neither the initialization statement nor the body, both of
// which carry a different relation tag.
TEST_F(For, ForIncrementIterationIsEmptyWithoutIncrementStatements) {
  VpiObject init;
  init.type = vpiForInitStmt;
  VpiObject condition;
  condition.type = vpiOperation;
  VpiObject body;
  body.type = vpiStmt;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&init, &condition, &body};

  EXPECT_EQ(ctx_.Iterate(vpiForIncStmt, &for_stmt), nullptr);
}

}  // namespace
}  // namespace delta
