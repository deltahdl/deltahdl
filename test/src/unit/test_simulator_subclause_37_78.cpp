#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.78 Return statement: the object model diagram for a return statement. The
// clause carries no BNF, no numbered Details, and no 'shall' sentences - it is
// the diagram alone, and the diagram draws a single edge: a controlling
// expression reached through vpiCondition. That expression is the value the
// return statement yields.
//
// The edge needs dedicated production code because the value's own type is an
// expression kind (an operation, a reference, a constant, ...), not the
// vpiCondition relation tag, so the generic child walk in vpi_handle - which
// matches by exact relation tag - cannot find it. This is the same situation as
// the controlling conditions of the while/repeat (§37.66), if/if-else (§37.71),
// for (§37.74), and do-while (§37.75) statements. A return that yields no value
// (a void function or task return) draws no such edge. These tests observe the
// production path applying the rule through the public vpi_handle dispatch.

// The fixture installs a context so the public vpi_handle entry point runs its
// real dispatch over the test objects.
class ReturnStatement : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Condition edge (vpiCondition -> expr): a return statement reaches the value
// it returns through the public vpi_handle(vpiCondition, ...) dispatch. The
// scan is type-directed: when the return object also carries a child of a kind
// the clause draws no edge to, the dispatch skips it and returns the value
// expression rather than the first child. The child that stands for that here
// is a statement, which carries the kind a statement of a design carries -
// §37.4.1 makes the dotted `stmt` enclosure the name of a class grouping other
// objects rather than a kind any object has, so a child typed vpiStmt was one
// no design could hold and the case it was written to make was not made.
TEST_F(ReturnStatement, ReturnReachesReturnedValueAmongOtherChildren) {
  VpiObject other;
  other.type = vpiNullStmt;  // not an expression, listed first
  VpiObject value;
  value.type = vpiOperation;  // the returned value: an expression kind

  VpiObject return_stmt;
  return_stmt.type = vpiReturnStmt;
  return_stmt.children = {&other, &value};

  EXPECT_EQ(vpi_handle(vpiCondition, &return_stmt), &value);
}

// Condition edge: the value is reached whatever expression kind it is written
// as. §37.59's `expr` class groups the operations, constants and calls, and
// through the `simple expr` class §37.58 nests inside it, the references,
// parameters and selects as well - a return yields any of them.
TEST_F(ReturnStatement, EachExpressionKindAValueCarriesIsReached) {
  for (int value_kind : {vpiOperation, vpiConstant, vpiRefObj, vpiFuncCall,
                         vpiParameter, vpiBitSelect}) {
    VpiObject value;
    value.type = value_kind;

    VpiObject return_stmt;
    return_stmt.type = vpiReturnStmt;
    return_stmt.children = {&value};

    EXPECT_EQ(vpi_handle(vpiCondition, &return_stmt), &value)
        << "value kind " << value_kind;
  }
}

// Condition edge reports no expression when the return statement yields no
// value - a return from a void function or a task. The scan finds no expression
// child and returns null.
TEST_F(ReturnStatement, VoidReturnReportsNoValue) {
  VpiObject return_stmt;
  return_stmt.type = vpiReturnStmt;

  EXPECT_EQ(vpi_handle(vpiCondition, &return_stmt), nullptr);
}

// Condition gating: the return-value relation is scoped to the return statement
// kind, so it does not disturb the vpiCondition edge other objects draw. A
// non-return object carrying an expression child is left to the generic
// traversal, which matches by exact relation tag and so does not surface that
// expression.
TEST_F(ReturnStatement, ReturnConditionRelationIsScopedToReturnStatements) {
  VpiObject expr;
  expr.type = vpiOperation;

  VpiObject not_a_return;
  not_a_return.type = vpiBegin;  // not a return statement
  not_a_return.children = {&expr};

  EXPECT_EQ(vpi_handle(vpiCondition, &not_a_return), nullptr);
}

}  // namespace
}  // namespace delta
