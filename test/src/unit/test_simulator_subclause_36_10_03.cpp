#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class TraversingExpressions : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  void TraverseOperands(vpiHandle expr) {
    vpiHandle sub_expr_i = vpi_iterate(vpiOperand, expr);
    if (sub_expr_i == nullptr) return;
    while (vpiHandle sub_expr_h = vpi_scan(sub_expr_i)) {
      TraverseExpr(sub_expr_h);
    }
  }

  void TraverseExpr(vpiHandle expr) {
    if (vpi_get(vpiType, expr) == vpiOperation) {
      TraverseOperands(expr);
      return;
    }
    leaves_.push_back(expr);
  }

  std::vector<vpiHandle> leaves_;
  VpiContext ctx_;
};

TEST_F(TraversingExpressions, AnOperationReachesItsOperands) {
  VpiObject left;
  left.type = vpiConstant;
  VpiObject right;
  right.type = vpiRefObj;

  VpiObject sum;
  sum.type = vpiOperation;
  sum.op_type = vpiAddOp;
  sum.children = {&left, &right};

  vpiHandle it = vpi_iterate(vpiOperand, VpiHandleOf(&sum));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &left);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &right);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

TEST_F(TraversingExpressions, TheClausesRoutineArrivesAtEveryLeaf) {
  VpiObject a;
  a.type = vpiConstant;
  VpiObject b;
  b.type = vpiRefObj;
  VpiObject inner;
  inner.type = vpiOperation;
  inner.op_type = vpiAddOp;
  inner.children = {&a, &b};

  VpiObject c;
  c.type = vpiConstant;
  VpiObject outer;
  outer.type = vpiOperation;
  outer.op_type = vpiMultOp;
  outer.children = {&inner, &c};

  TraverseExpr(VpiHandleOf(&outer));

  ASSERT_EQ(leaves_.size(), 3u);
  EXPECT_EQ(VpiObjectOf(leaves_[0]), &a);
  EXPECT_EQ(VpiObjectOf(leaves_[1]), &b);
  EXPECT_EQ(VpiObjectOf(leaves_[2]), &c);
}

TEST_F(TraversingExpressions, ANullOperationTakesNoOperands) {
  VpiObject null_op;
  null_op.type = vpiOperation;
  null_op.op_type = vpiNullOp;

  EXPECT_EQ(vpi_get(vpiOpType, VpiHandleOf(&null_op)), vpiNullOp);
  EXPECT_EQ(vpi_iterate(vpiOperand, VpiHandleOf(&null_op)), nullptr);

  TraverseExpr(VpiHandleOf(&null_op));
  EXPECT_TRUE(leaves_.empty());
}

TEST_F(TraversingExpressions, TheRelationIsTheOperationsOwn) {
  VpiObject child;
  child.type = vpiConstant;

  VpiObject leaf;
  leaf.type = vpiRefObj;
  leaf.children = {&child};

  EXPECT_EQ(vpi_iterate(vpiOperand, VpiHandleOf(&leaf)), nullptr);
}

}  // namespace
}  // namespace delta
