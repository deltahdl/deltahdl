#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.75 Do-while, foreach: the VPI object model for a do-while statement and a
// foreach statement. The clause carries two diagrams and two numbered Details.
//
// The do-while diagram draws a controlling condition expression (vpiCondition)
// and an unlabeled edge to a body statement (the generic vpiStmt relation). As
// with the other looping and conditional statements (§37.66/§37.71/§37.74), the
// condition's own type is an expression kind rather than the vpiCondition
// relation tag, so it needs dedicated production code; the body is a
// statement-edge child served by the generic traversal.
//
// The foreach diagram draws the indexed variable (vpiVariables), the loop's
// index variables (vpiLoopVars), and an unlabeled edge to a body statement. Its
// two Details are this clause's own rules:
//   D1 - the variable reached from a foreach statement via vpiVariables
//        represents the packed array, unpacked array, or string var being
//        indexed (the designated-pointer Handle case).
//   D2 - the vpiLoopVars iteration returns the foreach statement's index
//        variables in left-to-right order, with a skipped position reported as
//        a vpiOperation whose vpiOpType is vpiNullOp (the dedicated loop-var
//        walk of Iterate, shared with the foreach constraint of §37.38).
//
// The tests below observe the production code applying each rule through the
// public vpi_handle/vpi_iterate/vpi_scan/vpi_get entry points.

// The fixture installs a context so the public dispatch runs over the test
// objects.
class DoWhileForeach : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Do-while condition edge (vpiCondition -> expr): a do-while statement reaches
// its controlling condition through the public vpi_handle(vpiCondition, ...)
// dispatch. The scan is type-directed: it skips the body statement and returns
// the condition expression rather than the first child.
TEST_F(DoWhileForeach, DoWhileReachesConditionAmongConditionAndBody) {
  VpiObject body;
  body.type = vpiStmt;  // the body (the diagram's unlabeled edge), listed first
  VpiObject condition;
  condition.type = vpiOperation;  // the condition: an expression kind

  VpiObject do_while;
  do_while.type = vpiDoWhile;
  do_while.children = {&body, &condition};

  EXPECT_EQ(vpi_handle(vpiCondition, &do_while), &condition);
}

// Do-while condition reports no expression when the statement carries no
// condition child: the scan finds no expression among the statement-edge
// children and returns null.
TEST_F(DoWhileForeach, DoWhileWithoutConditionReportsNoCondition) {
  VpiObject body;
  body.type = vpiStmt;

  VpiObject do_while;
  do_while.type = vpiDoWhile;
  do_while.children = {&body};

  EXPECT_EQ(vpi_handle(vpiCondition, &do_while), nullptr);
}

// Do-while condition gating: the do-while condition relation is scoped to the
// do-while kind, so it does not disturb the vpiCondition edge other objects
// draw. A non-do-while object carrying an expression child is left to the
// generic traversal, which matches by exact relation tag and so does not
// surface that expression.
TEST_F(DoWhileForeach, DoWhileConditionRelationIsScopedToDoWhile) {
  VpiObject expr;
  expr.type = vpiOperation;

  VpiObject not_a_do_while;
  not_a_do_while.type = vpiBegin;  // not a do-while statement
  not_a_do_while.children = {&expr};

  EXPECT_EQ(vpi_handle(vpiCondition, &not_a_do_while), nullptr);
}

// Do-while body edge (the diagram's unlabeled arrow to a statement): a do-while
// statement reaches its body through the public vpi_handle(vpiStmt, ...)
// dispatch. The generic vpiStmt traversal is type-directed: it skips the
// condition child and returns the body statement.
TEST_F(DoWhileForeach, DoWhileReachesBodyThroughVpiStmt) {
  VpiObject condition;
  condition.type = vpiOperation;
  VpiObject body;
  body.type = vpiStmt;

  VpiObject do_while;
  do_while.type = vpiDoWhile;
  do_while.children = {&condition, &body};

  EXPECT_EQ(vpi_handle(vpiStmt, &do_while), &body);
}

// D1: a foreach statement's vpiVariables relation reaches the variable that
// represents the array being indexed - here a packed array variable. That
// variable's own type is a variable kind, so it is held as a designated pointer
// and reached through the scoped Handle case rather than a generic child match.
TEST_F(DoWhileForeach, ForeachStatementVariablesReachesIndexedArray) {
  VpiObject array;
  array.type = vpiPackedArrayVar;  // the packed array the foreach iterates over

  VpiObject foreach;
  foreach
    .type = vpiForeachStmt;
  foreach
    .foreach_array = &array;

  EXPECT_EQ(vpi_handle(vpiVariables, &foreach), &array);
}

// D1: the relation reports NULL when no indexed variable is attached. The
// scoped Handle case still fires for the foreach statement kind, but the
// designated pointer is null, so the relation yields nothing.
TEST_F(DoWhileForeach, ForeachStatementVariablesReportsNoVariableWhenAbsent) {
  VpiObject foreach;
  foreach
    .type = vpiForeachStmt;  // no indexed variable attached

  EXPECT_EQ(vpi_handle(vpiVariables, &foreach), nullptr);
}

// D1: the foreach-statement vpiVariables case is specific to a foreach
// statement. A different object kind is left to the generic traversal: its
// designated foreach_array pointer is ignored and a child whose own type is
// literally vpiVariables is returned instead.
TEST_F(DoWhileForeach, ForeachStatementVariablesIsScopedToForeachStatements) {
  VpiObject distractor_array;
  distractor_array.type = vpiPackedArrayVar;
  VpiObject vars_child;
  vars_child.type = vpiVariables;

  VpiObject not_a_foreach;
  not_a_foreach.type = vpiBegin;                    // not a foreach statement
  not_a_foreach.foreach_array = &distractor_array;  // must be ignored here
  not_a_foreach.children = {&vars_child};

  EXPECT_EQ(vpi_handle(vpiVariables, &not_a_foreach), &vars_child);
}

// D2: the vpiLoopVars iteration returns the foreach statement's index variables
// in left-to-right order, reached from the statement's dedicated loop-var list
// (not by matching children whose own type is literally vpiLoopVars). A skipped
// index position - stored as a null slot in the list - comes back as a freshly
// built placeholder operation whose operator is the null operation (vpiNullOp),
// so the caller still sees something occupying that slot. The real index
// variables on either side of the skip confirm the left-to-right order.
TEST_F(DoWhileForeach, ForeachStatementSkippedIndexIsNullOpPlaceholder) {
  VpiObject var_i;
  var_i.type = vpiIntegerVar;
  VpiObject var_k;
  var_k.type = vpiIntegerVar;

  VpiObject foreach;
  foreach
    .type = vpiForeachStmt;
  foreach
    .loop_vars = {&var_i, nullptr, &var_k};  // middle index skipped

  vpiHandle it = vpi_iterate(vpiLoopVars, &foreach);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(vpi_scan(it), &var_i);
  vpiHandle skipped = vpi_scan(it);
  ASSERT_NE(skipped, nullptr);
  EXPECT_NE(skipped, &var_i);  // the skipped slot is a fresh placeholder
  EXPECT_NE(skipped, &var_k);
  EXPECT_EQ(vpi_get(vpiType, skipped), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, skipped), vpiNullOp);
  EXPECT_EQ(vpi_scan(it), &var_k);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

// D2 edge case: when several index positions are skipped - here the first and
// the last, surrounding a single named index - each skip is reported as its own
// freshly built null-op placeholder. The two placeholders are distinct objects
// (one per slot), and the named index keeps its middle position, confirming the
// left-to-right walk handles boundary skips and back-to-back placeholder
// construction.
TEST_F(DoWhileForeach,
       ForeachStatementBoundarySkipsEachGetDistinctNullOpPlaceholder) {
  VpiObject var_j;
  var_j.type = vpiIntegerVar;

  VpiObject foreach;
  foreach
    .type = vpiForeachStmt;
  foreach
    .loop_vars = {nullptr, &var_j, nullptr};  // leading and trailing skip

  vpiHandle it = vpi_iterate(vpiLoopVars, &foreach);
  ASSERT_NE(it, nullptr);

  vpiHandle first_skip = vpi_scan(it);
  ASSERT_NE(first_skip, nullptr);
  EXPECT_EQ(vpi_get(vpiType, first_skip), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, first_skip), vpiNullOp);

  EXPECT_EQ(vpi_scan(it), &var_j);  // the named index keeps its middle slot

  vpiHandle last_skip = vpi_scan(it);
  ASSERT_NE(last_skip, nullptr);
  EXPECT_EQ(vpi_get(vpiType, last_skip), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, last_skip), vpiNullOp);

  EXPECT_NE(first_skip, last_skip);  // each skipped slot is its own placeholder
  EXPECT_EQ(vpi_scan(it), nullptr);
}

// Foreach body edge (the diagram's unlabeled arrow to a statement): a foreach
// statement reaches its body through the public vpi_handle(vpiStmt, ...)
// dispatch. The generic vpiStmt traversal is type-directed and returns the body
// statement; the indexed-variable and loop-variable edges are reached through
// their own dedicated relations and are not statement-tagged children, so they
// do not interfere.
TEST_F(DoWhileForeach, ForeachStatementReachesBodyThroughVpiStmt) {
  VpiObject array;
  array.type = vpiPackedArrayVar;  // the indexed variable (its own relation)
  VpiObject body;
  body.type = vpiStmt;  // the body (the diagram's unlabeled edge)

  VpiObject foreach;
  foreach
    .type = vpiForeachStmt;
  foreach
    .foreach_array = &array;
  foreach
    .children = {&body};

  EXPECT_EQ(vpi_handle(vpiStmt, &foreach), &body);
}

// D2: the loop-var iteration is scoped to the foreach statement kind. A
// different object kind carrying a loop-var list does not have it walked: the
// iteration falls to the generic handling, which matches children whose own
// type is literally vpiLoopVars - of which there are none - and so reports
// nothing.
TEST_F(DoWhileForeach,
       ForeachStatementLoopVarsIterationIsScopedToForeachStatements) {
  VpiObject var_i;
  var_i.type = vpiIntegerVar;

  VpiObject not_a_foreach;
  not_a_foreach.type = vpiBegin;       // not a foreach statement
  not_a_foreach.loop_vars = {&var_i};  // must not be walked here

  EXPECT_EQ(vpi_iterate(vpiLoopVars, &not_a_foreach), nullptr);
}

}  // namespace
}  // namespace delta
