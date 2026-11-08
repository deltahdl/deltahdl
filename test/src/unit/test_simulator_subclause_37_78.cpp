#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ReturnStatement : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(ReturnStatement, ReturnReachesReturnedValueAmongOtherChildren) {
  VpiObject other;
  other.type = vpiNullStmt;
  VpiObject value;
  value.type = vpiOperation;

  VpiObject return_stmt;
  return_stmt.type = vpiReturnStmt;
  return_stmt.children = {&other, &value};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&return_stmt))),
            &value);
}

TEST_F(ReturnStatement, EachExpressionKindAValueCarriesIsReached) {
  for (int value_kind : {vpiOperation, vpiConstant, vpiRefObj, vpiFuncCall,
                         vpiParameter, vpiBitSelect}) {
    VpiObject value;
    value.type = value_kind;

    VpiObject return_stmt;
    return_stmt.type = vpiReturnStmt;
    return_stmt.children = {&value};

    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&return_stmt))),
              &value)
        << "value kind " << value_kind;
  }
}

TEST_F(ReturnStatement, VoidReturnReportsNoValue) {
  VpiObject return_stmt;
  return_stmt.type = vpiReturnStmt;

  EXPECT_EQ(vpi_handle(vpiCondition, VpiHandleOf(&return_stmt)), nullptr);
}

TEST_F(ReturnStatement, ReturnConditionRelationIsScopedToReturnStatements) {
  VpiObject expr;
  expr.type = vpiOperation;

  VpiObject not_a_return;
  not_a_return.type = vpiBegin;
  not_a_return.children = {&expr};

  EXPECT_EQ(vpi_handle(vpiCondition, VpiHandleOf(&not_a_return)), nullptr);
}

TEST(ReturnModel, NoObjectHasNoReturnExpression) {
  EXPECT_EQ(VpiReturnConditionExpr(nullptr), nullptr);
}

}  // namespace
}  // namespace delta
