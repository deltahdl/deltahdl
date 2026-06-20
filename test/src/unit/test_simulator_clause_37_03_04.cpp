#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.3.4 Delays and values: nets, primitives, module paths, timing checks, and
// continuous assignments can carry a delay written within the SystemVerilog
// source. The vpiDelay relation reaches the expression standing for that source
// delay. Two normative "shall" rules constrain the form of that expression:
//   - Claim S1: the expression shall be one that evaluates to a constant when a
//     single delay is specified, or an operation when more than one delay is
//     specified.
//   - Claim S2: in the multiple-delay case the operation's vpiOpType shall be
//     vpiListOp.
// The rest of the subclause (the vpi_get_delays/vpi_put_delays/vpi_get_value/
// vpi_put_value routines and their structures, the actual delays the tool uses)
// is descriptive of, or a pointer to, Clause 38, which owns those rules. These
// tests observe the production helpers in vpi.cpp - and the VpiContext::Handle
// dispatch they feed - that apply the vpiDelay access and the S1/S2 form rules.

// D2 grouping: the object kinds whose delays are written in the source and are
// therefore reachable through vpiDelay - a net, a primitive (and its gate,
// switch, and udp forms), a module path, a timing check, and a continuous
// assignment. An unrelated object kind carries no source delay.
TEST(SourceDelayModel, DelayCarryingTypeClassification) {
  EXPECT_TRUE(VpiObjectCarriesSourceDelay(vpiNet));
  EXPECT_TRUE(VpiObjectCarriesSourceDelay(vpiPrimitive));
  EXPECT_TRUE(VpiObjectCarriesSourceDelay(vpiGate));
  EXPECT_TRUE(VpiObjectCarriesSourceDelay(vpiSwitch));
  EXPECT_TRUE(VpiObjectCarriesSourceDelay(vpiUdp));
  EXPECT_TRUE(VpiObjectCarriesSourceDelay(vpiModPath));
  EXPECT_TRUE(VpiObjectCarriesSourceDelay(vpiTchk));
  EXPECT_TRUE(VpiObjectCarriesSourceDelay(vpiContAssign));
  // A module, by contrast, carries no source-written delay reached this way.
  EXPECT_FALSE(VpiObjectCarriesSourceDelay(vpiModule));
}

// D2 + S1 (single delay): vpiDelay of a delay-carrying object reaches its
// designated source-delay expression. With one delay specified, that expression
// is a single constant-valued expression.
TEST(SourceDelayModel, SingleDelayReachesConstantExpression) {
  VpiObject net;
  net.type = vpiNet;
  VpiObject
      delay;  // one delay specified -> an expression evaluating to a const
  delay.type = vpiConstant;
  net.delay_expr = &delay;

  EXPECT_EQ(VpiSourceDelayExpr(&net), &delay);
  // A single constant-valued delay is not the multiple-delay list operation.
  EXPECT_FALSE(VpiSourceDelayExprIsListOp(VpiSourceDelayExpr(&net)));
}

// D2 (edges): a null handle, an object that is not a delay-carrying kind, and a
// delay-carrying object with no source delay all reach no delay expression.
TEST(SourceDelayModel, NoDelayExpressionReachesNull) {
  EXPECT_EQ(VpiSourceDelayExpr(nullptr), nullptr);

  VpiObject delay;
  delay.type = vpiConstant;

  // The delay is carried by the wrong object kind: a module is not reachable.
  VpiObject module;
  module.type = vpiModule;
  module.delay_expr = &delay;
  EXPECT_EQ(VpiSourceDelayExpr(&module), nullptr);

  // A delay-carrying kind with no source delay reaches nothing.
  VpiObject net;
  net.type = vpiNet;
  EXPECT_EQ(VpiSourceDelayExpr(&net), nullptr);
}

// S1 + S2 (multiple delays): when more than one delay is specified the vpiDelay
// expression shall be an operation whose vpiOpType is vpiListOp.
TEST(SourceDelayModel, MultipleDelaysAreListOperation) {
  VpiObject list_op;
  list_op.type = vpiOperation;
  list_op.op_type = vpiListOp;
  EXPECT_TRUE(VpiSourceDelayExprIsListOp(&list_op));

  // A single constant-valued delay (the one-delay form) is not the list op.
  VpiObject constant;
  constant.type = vpiConstant;
  EXPECT_FALSE(VpiSourceDelayExprIsListOp(&constant));

  // A different operation type does not satisfy the rule, and neither does a
  // null handle.
  VpiObject other_op;
  other_op.type = vpiOperation;
  other_op.op_type = vpiConcatOp;
  EXPECT_FALSE(VpiSourceDelayExprIsListOp(&other_op));
  EXPECT_FALSE(VpiSourceDelayExprIsListOp(nullptr));
}

// D2 + S1 (public path, single delay): traversing vpiDelay through the public
// handle dispatch returns the source-delay expression, and for one delay it is
// the constant-valued expression rather than a list operation.
TEST(SourceDelayPublic, HandleDelayReturnsSingleConstantExpression) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject cont_assign;
  cont_assign.type = vpiContAssign;
  VpiObject delay;
  delay.type = vpiConstant;
  cont_assign.delay_expr = &delay;

  VpiHandle expr = ctx.Handle(vpiDelay, &cont_assign);
  ASSERT_EQ(expr, &delay);
  EXPECT_EQ(ctx.Get(vpiType, expr), vpiConstant);
  EXPECT_FALSE(VpiSourceDelayExprIsListOp(expr));

  SetGlobalVpiContext(nullptr);
}

// S1 + S2 (public path, multiple delays): traversing vpiDelay returns the list
// operation, and the object it returns satisfies the type/op-type rule.
TEST(SourceDelayPublic, HandleDelayReturnsListOperationForMultipleDelays) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject mod_path;
  mod_path.type = vpiModPath;
  VpiObject op;
  op.type = vpiOperation;
  op.op_type = vpiListOp;
  mod_path.delay_expr = &op;

  VpiHandle expr = ctx.Handle(vpiDelay, &mod_path);
  ASSERT_EQ(expr, &op);
  EXPECT_EQ(ctx.Get(vpiType, expr), vpiOperation);
  EXPECT_EQ(ctx.Get(vpiOpType, expr), vpiListOp);
  EXPECT_TRUE(VpiSourceDelayExprIsListOp(expr));

  SetGlobalVpiContext(nullptr);
}

// D2 (public path edge): vpiDelay is diverted only for the delay-carrying
// object kinds; an object that does not carry a source delay is not diverted,
// so the public path reaches nothing.
TEST(SourceDelayPublic, HandleDelayNotDivertedForNonDelayObject) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject delay;
  delay.type = vpiConstant;
  VpiObject module;
  module.type = vpiModule;
  module.delay_expr = &delay;

  EXPECT_EQ(ctx.Handle(vpiDelay, &module), nullptr);

  SetGlobalVpiContext(nullptr);
}

}  // namespace
}  // namespace delta
