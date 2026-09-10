#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §36.10.3 (Traversing expressions) says how an application walks an expression
// the source wrote: "Expressions with multiple operands will result in a handle
// of type vpiOperation. To determine how many operands, access the property
// vpiOpType. This operation will be evaluated after its subexpressions.
// Therefore, it has the least precedence in the expression." It then prints the
// routine that does the walking - traverseExpr(), which switches on
// vpi_get(vpiType, expr), and for a vpiOperation iterates vpiOperand and
// recurses into each operand vpi_scan() hands back.
//
// Nothing served vpiOperand. It is a relation tag and no object's type is one,
// so the generic traversal - which looks for a child whose own type is the type
// asked for - reached no operand of any operation, and the routine the clause
// prints descended into nothing.
class TraversingExpressions : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // The operation arm of §36.10.3's traverseExpr(): iterate vpiOperand and
  // recurse into each operand vpi_scan() hands back.
  void TraverseOperands(vpiHandle expr) {
    vpiHandle sub_expr_i = vpi_iterate(vpiOperand, expr);
    if (sub_expr_i == nullptr) return;  // else it is of op type vpiNullOp
    while (vpiHandle sub_expr_h = vpi_scan(sub_expr_i)) {
      TraverseExpr(sub_expr_h);
    }
  }

  // §36.10.3's own traverseExpr(), with the leaves recorded rather than
  // processed so a case can say which of them the walk arrived at. The clause
  // writes the two arms as a switch on vpi_get(vpiType, expr); they are written
  // here as the operation test and the default beside it, which the nesting
  // limit clang-tidy holds a test function under leaves room for.
  void TraverseExpr(vpiHandle expr) {
    if (vpi_get(vpiType, expr) == vpiOperation) {
      TraverseOperands(expr);
      return;
    }
    leaves_.push_back(expr);  // do whatever to the leaf object
  }

  std::vector<vpiHandle> leaves_;
  VpiContext ctx_;
};

// §36.10.3: an operation reaches the operands it was written with, in that
// order. They carry their own expression kinds, which is what the recursion in
// the clause's routine switches on.
TEST_F(TraversingExpressions, AnOperationReachesItsOperands) {
  VpiObject left;
  left.type = vpiConstant;
  VpiObject right;
  right.type = vpiRefObj;

  VpiObject sum;
  sum.type = vpiOperation;
  sum.op_type = vpiAddOp;
  sum.children = {&left, &right};

  vpiHandle it = vpi_iterate(vpiOperand, &sum);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(vpi_scan(it), &left);
  EXPECT_EQ(vpi_scan(it), &right);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

// §36.10.3: the clause's routine run over a complex expression. The operation
// standing over the others is evaluated after its subexpressions, so the walk
// descends through it and arrives at every leaf, in written order.
TEST_F(TraversingExpressions, TheClausesRoutineArrivesAtEveryLeaf) {
  VpiObject a;
  a.type = vpiConstant;
  VpiObject b;
  b.type = vpiRefObj;
  VpiObject inner;  // a + b, the subexpression evaluated first
  inner.type = vpiOperation;
  inner.op_type = vpiAddOp;
  inner.children = {&a, &b};

  VpiObject c;
  c.type = vpiConstant;
  VpiObject outer;  // (a + b) * c, the least precedence in the expression
  outer.type = vpiOperation;
  outer.op_type = vpiMultOp;
  outer.children = {&inner, &c};

  TraverseExpr(&outer);

  ASSERT_EQ(leaves_.size(), 3u);
  EXPECT_EQ(leaves_[0], &a);
  EXPECT_EQ(leaves_[1], &b);
  EXPECT_EQ(leaves_[2], &c);
}

// §36.10.3: "To determine how many operands, access the property vpiOpType." A
// null operation takes none, which is the case the clause's routine comments on
// where the iteration yields no iterator.
TEST_F(TraversingExpressions, ANullOperationTakesNoOperands) {
  VpiObject null_op;
  null_op.type = vpiOperation;
  null_op.op_type = vpiNullOp;

  EXPECT_EQ(vpi_get(vpiOpType, &null_op), vpiNullOp);
  EXPECT_EQ(vpi_iterate(vpiOperand, &null_op), nullptr);

  TraverseExpr(&null_op);
  EXPECT_TRUE(leaves_.empty());
}

// §36.10.3: the relation belongs to the operation. A leaf the walk arrives at
// is not one, so asking it for operands reaches none even when it carries
// expression children of its own.
TEST_F(TraversingExpressions, TheRelationIsTheOperationsOwn) {
  VpiObject child;
  child.type = vpiConstant;

  VpiObject leaf;
  leaf.type = vpiRefObj;
  leaf.children = {&child};

  EXPECT_EQ(vpi_iterate(vpiOperand, &leaf), nullptr);
}

}  // namespace
}  // namespace delta
