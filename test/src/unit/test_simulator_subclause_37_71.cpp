#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.71 If, if-else: the object model diagram draws a dotted enclosure holding
// a plain if statement and an if-else statement. From the enclosure it draws a
// vpiCondition edge to a controlling condition expression and an unlabeled edge
// to a body statement - the then-branch the condition selects, whose relation
// §37.4.3 names by putting "vpi" in front of the target enclosure's words - and
// from the if-else alone a vpiElseStmt edge to a second body statement. Both
// kinds carry an int vpiQualifier property (the unique/priority qualifier
// flags). The clause has no numbered Details and no 'shall' sentences.
//
// §37.4.1 makes a dotted enclosure a class that groups other objects and
// classes rather than a kind of its own, so both branches carry the kind a
// statement of a design carries - a begin, an assignment, another if - and
// neither carries vpiStmt, which is the class's name. Read the other way, as a
// child whose own type is the relation tag, the then-branch of every
// conditional was reached by nothing and the else-branch, which is found by
// counting statement children, was never reached either because the count never
// got past the first. These tests observe the production path for each edge:
// the condition through VpiIfConditionExpr, the then-branch through the body
// resolver the process, loop, wait and forever kinds share, and the
// else-branch through VpiIfElseStmt, all reached by their public dispatch.

// The fixture installs a context so the public vpi_handle / vpi_get entry
// points run their real dispatch over the test objects.
class IfIfElse : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// vpiCondition edge: a plain if statement reaches its condition expression
// through the public vpi_handle(vpiCondition, ...) dispatch path.
TEST_F(IfIfElse, IfStatementReachesConditionThroughVpiCondition) {
  VpiObject condition;
  condition.type = vpiOperation;  // an expression kind

  VpiObject then_body;
  then_body.type = vpiBegin;  // a kind the `stmt` class groups

  VpiObject if_stmt;
  if_stmt.type = vpiIf;
  if_stmt.children = {&condition, &then_body};

  EXPECT_EQ(vpi_handle(vpiCondition, &if_stmt), &condition);
}

// vpiCondition edge: an if-else statement reaches its condition the same way -
// the edge is drawn from the enclosure, so it serves both conditional kinds.
TEST_F(IfIfElse, IfElseStatementReachesConditionThroughVpiCondition) {
  VpiObject condition;
  condition.type = vpiRefObj;  // another expression kind

  VpiObject then_body;
  then_body.type = vpiBegin;

  VpiObject else_body;
  else_body.type = vpiAssignment;

  VpiObject if_else;
  if_else.type = vpiIfElse;
  if_else.children = {&condition, &then_body, &else_body};

  EXPECT_EQ(vpi_handle(vpiCondition, &if_else), &condition);
}

// vpiCondition edge: the condition is found even when a body statement precedes
// it in the child list. The scan skips the body and returns the first
// expression child.
TEST_F(IfIfElse, ConditionFoundWhenItFollowsABodyChild) {
  VpiObject then_body;
  then_body.type = vpiBegin;  // a statement, not an expression, listed first

  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject if_stmt;
  if_stmt.type = vpiIf;
  if_stmt.children = {&then_body, &condition};

  EXPECT_EQ(vpi_handle(vpiCondition, &if_stmt), &condition);
}

// vpiCondition edge is scoped to the conditional statements: asking some other
// statement kind for vpiCondition does not pick up an expression child through
// this path. A repeat control (§37.69 draws its own edges) with an expression
// child yields no condition from the if/if-else dispatch.
TEST_F(IfIfElse, VpiConditionIsScopedToConditionalStatements) {
  VpiObject expr;
  expr.type = vpiOperation;

  VpiObject other;
  other.type = vpiRepeatControl;
  other.children = {&expr};

  EXPECT_EQ(vpi_handle(vpiCondition, &other), nullptr);
}

// vpiCondition edge, no-condition edge case: a conditional statement that
// carries only body statements (no expression child) yields no condition. This
// reaches the dedicated VpiIfConditionExpr scan - distinct from the scoped test
// above, which is rejected at the type gate before the scan runs - and observes
// the scan completing over the children without finding an expression.
TEST_F(IfIfElse, ConditionIsNullWhenNoExpressionChild) {
  VpiObject then_body;
  then_body.type = vpiBegin;

  VpiObject if_stmt;
  if_stmt.type = vpiIf;
  if_stmt.children = {&then_body};

  EXPECT_EQ(vpi_handle(vpiStmt, &if_stmt), &then_body);
  EXPECT_EQ(vpi_handle(vpiCondition, &if_stmt), nullptr);
}

// Then-branch edge (the enclosure's unlabeled arrow to `stmt`): an if-else
// statement reaches the branch the condition selects through
// vpi_handle(vpiStmt, ...) - the first statement child, told from the
// else-branch by position.
TEST_F(IfIfElse, ThenBodyReachedByTheKindTheStmtClassGroups) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject then_body;
  then_body.type = vpiBegin;

  VpiObject else_body;
  else_body.type = vpiAssignment;

  VpiObject if_else;
  if_else.type = vpiIfElse;
  if_else.children = {&condition, &then_body, &else_body};

  EXPECT_EQ(vpi_handle(vpiStmt, &if_else), &then_body);
}

// Then-branch edge: the arrow is drawn from the enclosure, so a plain if
// reaches its branch by it too, and it reaches one whatever kind the branch is
// written as - a lone statement, a block, or a nested conditional.
TEST_F(IfIfElse, PlainIfReachesEachKindAThenBranchCarries) {
  for (int body_kind :
       {vpiAssignment, vpiNamedBegin, vpiFork, vpiIf, vpiNullStmt}) {
    VpiObject condition;
    condition.type = vpiOperation;

    VpiObject then_body;
    then_body.type = body_kind;

    VpiObject if_stmt;
    if_stmt.type = vpiIf;
    if_stmt.children = {&condition, &then_body};

    EXPECT_EQ(vpi_handle(vpiStmt, &if_stmt), &then_body)
        << "then-branch kind " << body_kind;
  }
}

// vpiElseStmt edge: an if-else statement reaches its else-branch - the second
// statement child - through the public vpi_handle(vpiElseStmt, ...) dispatch,
// distinct from the then-branch the unlabeled arrow reaches.
TEST_F(IfIfElse, IfElseStatementReachesElseBranchThroughVpiElseStmt) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject then_body;
  then_body.type = vpiBegin;

  VpiObject else_body;
  else_body.type = vpiAssignment;

  VpiObject if_else;
  if_else.type = vpiIfElse;
  if_else.children = {&condition, &then_body, &else_body};

  EXPECT_EQ(vpi_handle(vpiStmt, &if_else), &then_body);
  EXPECT_EQ(vpi_handle(vpiElseStmt, &if_else), &else_body);
}

// vpiElseStmt edge: an else-branch written as a nested if - the else-if chain
// of 12.4 - is the second statement child like any other, and the two branches
// are told apart by position rather than by kind even where both carry the same
// one.
TEST_F(IfIfElse, ElseBranchWrittenAsANestedConditionalIsTheSecondStatement) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject then_body;
  then_body.type = vpiIf;

  VpiObject else_body;
  else_body.type = vpiIf;

  VpiObject if_else;
  if_else.type = vpiIfElse;
  if_else.children = {&condition, &then_body, &else_body};

  EXPECT_EQ(vpi_handle(vpiStmt, &if_else), &then_body);
  EXPECT_EQ(vpi_handle(vpiElseStmt, &if_else), &else_body);
}

// vpiElseStmt is drawn only from the if-else: a plain if reports no else branch
// even when it carries a second statement child, because the relation is gated
// on the if-else kind.
TEST_F(IfIfElse, PlainIfReportsNoElseStatement) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject then_body;
  then_body.type = vpiBegin;

  VpiObject second_body;
  second_body.type = vpiAssignment;

  VpiObject if_stmt;
  if_stmt.type = vpiIf;
  if_stmt.children = {&condition, &then_body, &second_body};

  EXPECT_EQ(vpi_handle(vpiElseStmt, &if_stmt), nullptr);
}

// vpiElseStmt edge: an if-else carrying only a then branch reports no else
// branch, so the one statement it holds is not handed back for both edges, and
// a null handle reports none either.
TEST_F(IfIfElse, ElseStatementIsNullWhenNoElseBranch) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject then_body;
  then_body.type = vpiBegin;

  VpiObject if_else;
  if_else.type = vpiIfElse;
  if_else.children = {&condition, &then_body};

  EXPECT_EQ(vpi_handle(vpiElseStmt, &if_else), nullptr);
  EXPECT_EQ(VpiIfElseStmt(nullptr), nullptr);
}

// Property (-> qualifier int: vpiQualifier): an if or if-else statement reports
// its qualifier flags (a bitwise OR of the unique/priority/etc. qualifiers,
// vpiNoQualifier when none) as an int property through the public vpi_get
// dispatch.
TEST_F(IfIfElse, ConditionalStatementReportsQualifier) {
  VpiObject if_stmt;
  if_stmt.type = vpiIf;
  if_stmt.qualifier = vpiUniqueQualifier;
  EXPECT_EQ(vpi_get(vpiQualifier, &if_stmt), vpiUniqueQualifier);

  VpiObject if_else;
  if_else.type = vpiIfElse;
  if_else.qualifier = vpiPriorityQualifier;
  EXPECT_EQ(vpi_get(vpiQualifier, &if_else), vpiPriorityQualifier);

  // An if statement written with no qualifier reports the "none" sentinel.
  VpiObject plain_if;
  plain_if.type = vpiIf;
  EXPECT_EQ(vpi_get(vpiQualifier, &plain_if), vpiNoQualifier);
}

}  // namespace
}  // namespace delta
