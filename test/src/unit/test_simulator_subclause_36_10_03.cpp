#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
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

class TraversingExpressionsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle RhsOfTheOnlyContinuousAssignment() {
    vpiHandle it = vpi_iterate(vpiContAssign, By("top"));
    if (it == nullptr) return nullptr;
    return vpi_handle(vpiRhs, vpi_scan(it));
  }

  void Walk(vpiHandle expr) {
    if (vpi_get(vpiType, expr) != vpiOperation) {
      const char* name = vpi_get_str(vpiName, expr);
      leaves_.emplace_back(name == nullptr ? "" : name);
      return;
    }
    vpiHandle it = vpi_iterate(vpiOperand, expr);
    if (it == nullptr) return;
    while (vpiHandle sub = vpi_scan(it)) Walk(sub);
  }

  std::vector<std::string> leaves_;
};

TEST_F(TraversingExpressionsOfARun, TheClausesRoutineWalksANestedSourceExpr) {
  Run("module top;\n"
      "  int a = 1, b = 2, c = 3;\n"
      "  wire [31:0] y;\n"
      "  assign y = (a + b) * c;\n"
      "  initial $noop;\n"
      "endmodule\n");
  vpiHandle rhs = RhsOfTheOnlyContinuousAssignment();
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(vpi_get(vpiType, rhs), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, rhs), vpiMultOp);
  const std::vector<vpiHandle> kOperands = ObjectsOf(vpiOperand, rhs);
  ASSERT_EQ(kOperands.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kOperands[0]), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, kOperands[0]), vpiAddOp);
  EXPECT_NE(vpi_get(vpiType, kOperands[1]), vpiOperation);
  Walk(rhs);
  EXPECT_EQ(leaves_, (std::vector<std::string>{"a", "b", "c"}));
}

TEST_F(TraversingExpressionsOfARun, TheLeastPrecedenceOperatorIsOutermost) {
  Run("module top;\n"
      "  int a = 1, b = 2, c = 3;\n"
      "  wire [31:0] y;\n"
      "  assign y = a + b * c;\n"
      "  initial $noop;\n"
      "endmodule\n");
  vpiHandle rhs = RhsOfTheOnlyContinuousAssignment();
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, rhs), vpiAddOp);
  const std::vector<vpiHandle> kOperands = ObjectsOf(vpiOperand, rhs);
  ASSERT_EQ(kOperands.size(), 2U);
  EXPECT_NE(vpi_get(vpiType, kOperands[0]), vpiOperation);
  EXPECT_STREQ(vpi_get_str(vpiName, kOperands[0]), "a");
  EXPECT_EQ(vpi_get(vpiType, kOperands[1]), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, kOperands[1]), vpiMultOp);
  Walk(rhs);
  EXPECT_EQ(leaves_, (std::vector<std::string>{"a", "b", "c"}));
}

}  // namespace
}  // namespace delta
