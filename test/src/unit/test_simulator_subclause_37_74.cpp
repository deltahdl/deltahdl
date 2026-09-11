#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.74 For: the object model diagram for a for statement. The clause carries
// no numbered Details, no 'shall' sentences and no BNF - it is the diagram
// alone, and the diagram draws six arrows. vpiForInitStmt and vpiForIncStmt are
// each drawn twice, once as a double arrow and once as a single one, which
// §37.4.3 makes a vpi_iterate() over every statement of that part of the header
// and a vpi_handle() to the first of them; a for header writes a comma list of
// either, which is what the pair is for. Beside them the diagram draws
// vpiCondition to an expr and an untagged arrow to the dotted `stmt` enclosure,
// which §37.4.3 names vpiStmt and which is the body the loop runs. The for
// object also carries the vpiLocalVarDecls property ("has local variables"),
// which is owned by §37.12 and is not retested here.
//
// §37.4.1 makes a dotted enclosure a class grouping other objects and classes
// rather than a kind, so an init statement, an increment statement and the body
// all carry the kind a statement of a design carries - an assignment, an
// increment operation, a begin - and none of them carries vpiForInitStmt,
// vpiForIncStmt or vpiStmt, which name the arrows. A type match cannot tell the
// three apart either, which is why the header's statements are held in the for
// statement's own init and increment lists and the body is the statement child
// the untagged arrow reaches. Read the other way, as children whose own types
// are the relation tags, the header of no for loop that could be written was
// reached at all. These tests observe each edge through its public dispatch.

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
// dispatch. The scan is type-directed, so it skips the body statement and
// returns the condition rather than the first child.
TEST_F(For, ForStatementReachesConditionAmongItsChildren) {
  VpiObject body;
  body.type = vpiBegin;  // a statement child, listed first
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&body, &condition};

  EXPECT_EQ(vpi_handle(vpiCondition, &for_stmt), &condition);
}

// Condition edge reports no expression when the for statement has no condition
// child - a for loop written without a controlling expression, which 12.7.1
// allows and which runs forever.
TEST_F(For, ForWithoutConditionReportsNoCondition) {
  VpiObject body;
  body.type = vpiBegin;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&body};

  EXPECT_EQ(vpi_handle(vpiCondition, &for_stmt), nullptr);
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

  EXPECT_EQ(vpi_handle(vpiCondition, &not_a_for), nullptr);
}

// Initialization double arrow: a for statement whose header writes a comma list
// of initialization statements reaches all of them, in source order, through
// the vpiForInitStmt iteration. They carry the kinds a statement of a design
// carries, and the increment statements and the body are not among them.
TEST_F(For, InitializationStatementsReachedThroughTheVpiForInitStmtIteration) {
  VpiObject init0;
  init0.type = vpiAssignment;
  VpiObject init1;
  init1.type = vpiAssignment;
  VpiObject increment;
  increment.type = vpiAssignment;
  VpiObject body;
  body.type = vpiBegin;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&body};
  for_stmt.for_init_stmts = {&init0, &init1};
  for_stmt.for_inc_stmts = {&increment};

  VpiHandle it = ctx_.Iterate(vpiForInitStmt, &for_stmt);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(ctx_.Scan(it), &init0);
  EXPECT_EQ(ctx_.Scan(it), &init1);
  EXPECT_EQ(ctx_.Scan(it), nullptr);  // drains; increment and body excluded
}

// Increment double arrow: symmetrically, the increment statements are reached
// through the vpiForIncStmt iteration, in order, and the initialization
// statements are not among them.
TEST_F(For, IncrementStatementsReachedThroughTheVpiForIncStmtIteration) {
  VpiObject init;
  init.type = vpiAssignment;
  VpiObject increment0;
  increment0.type = vpiAssignment;
  VpiObject increment1;
  increment1.type = vpiAssignment;
  VpiObject body;
  body.type = vpiBegin;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&body};
  for_stmt.for_init_stmts = {&init};
  for_stmt.for_inc_stmts = {&increment0, &increment1};

  VpiHandle it = ctx_.Iterate(vpiForIncStmt, &for_stmt);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(ctx_.Scan(it), &increment0);
  EXPECT_EQ(ctx_.Scan(it), &increment1);
  EXPECT_EQ(ctx_.Scan(it), nullptr);  // drains; init and body excluded
}

// The single arrows drawn beside those iterations: vpi_handle reaches the first
// statement of each part of the header, which is the whole of it for the common
// header that writes one of each.
TEST_F(For, SingleArrowsReachTheFirstStatementOfEachPartOfTheHeader) {
  VpiObject init0;
  init0.type = vpiAssignment;
  VpiObject init1;
  init1.type = vpiAssignment;
  VpiObject increment0;
  increment0.type = vpiAssignment;
  VpiObject increment1;
  increment1.type = vpiAssignment;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.for_init_stmts = {&init0, &init1};
  for_stmt.for_inc_stmts = {&increment0, &increment1};

  EXPECT_EQ(vpi_handle(vpiForInitStmt, &for_stmt), &init0);
  EXPECT_EQ(vpi_handle(vpiForIncStmt, &for_stmt), &increment0);
}

// Both relations report nothing for a header that writes neither part: the
// iterations are empty and the single arrows reach no statement. A for loop
// written "for (;;)" is the case.
TEST_F(For, AHeaderThatWritesNeitherPartReachesNothingByEitherRelation) {
  VpiObject body;
  body.type = vpiBegin;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&body};

  EXPECT_EQ(ctx_.Iterate(vpiForInitStmt, &for_stmt), nullptr);
  EXPECT_EQ(ctx_.Iterate(vpiForIncStmt, &for_stmt), nullptr);
  EXPECT_EQ(vpi_handle(vpiForInitStmt, &for_stmt), nullptr);
  EXPECT_EQ(vpi_handle(vpiForIncStmt, &for_stmt), nullptr);
}

// The header relations are scoped to the for statement: an object of another
// kind asked for either of them reaches nothing, so the lists are not read off
// an object the diagram does not draw them on.
TEST_F(For, HeaderRelationsAreScopedToForStatements) {
  VpiObject body;
  body.type = vpiBegin;

  VpiObject not_a_for;
  not_a_for.type = vpiWhile;
  not_a_for.children = {&body};

  EXPECT_EQ(vpi_handle(vpiForInitStmt, &not_a_for), nullptr);
  EXPECT_EQ(ctx_.Iterate(vpiForInitStmt, &not_a_for), nullptr);
}

// Body edge (the untagged arrow to `stmt`): a for statement reaches the body it
// loops over through vpi_handle(vpiStmt, ...) - the statement child, told from
// the condition by kind and from the header's statements by their being held
// apart from the children.
TEST_F(For, ForStatementReachesBodyByTheKindTheStmtClassGroups) {
  VpiObject condition;
  condition.type = vpiOperation;
  VpiObject init;
  init.type = vpiAssignment;
  VpiObject body;
  body.type = vpiBegin;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&condition, &body};
  for_stmt.for_init_stmts = {&init};

  EXPECT_EQ(vpi_handle(vpiStmt, &for_stmt), &body);
}

// Body edge: the body is reached whatever kind it is written as - a lone
// statement, a block, or a nested loop.
TEST_F(For, EachKindABodyCarriesIsReached) {
  for (int body_kind :
       {vpiAssignment, vpiNamedBegin, vpiFork, vpiFor, vpiNullStmt}) {
    VpiObject body;
    body.type = body_kind;

    VpiObject for_stmt;
    for_stmt.type = vpiFor;
    for_stmt.children = {&body};

    EXPECT_EQ(vpi_handle(vpiStmt, &for_stmt), &body)
        << "body kind " << body_kind;
  }
}

// Body edge edge case: a for statement carrying a condition and a header but no
// body statement reaches no body, and neither the condition nor a header
// statement is handed back in its place.
TEST_F(For, ForWithoutBodyReportsNoStatement) {
  VpiObject condition;
  condition.type = vpiOperation;
  VpiObject init;
  init.type = vpiAssignment;
  VpiObject increment;
  increment.type = vpiAssignment;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&condition};
  for_stmt.for_init_stmts = {&init};
  for_stmt.for_inc_stmts = {&increment};

  EXPECT_EQ(vpi_handle(vpiStmt, &for_stmt), nullptr);
}

}  // namespace
}  // namespace delta
