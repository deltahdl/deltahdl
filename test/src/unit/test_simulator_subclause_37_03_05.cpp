#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.3.5 (Expressions with side effects) governs how VPI behaves when an
// expression it reaches has side effects when evaluated - one built from an
// assignment or increment/decrement operator, a state-changing function or
// system-function call, or any expression containing such a subexpression as an
// operand, argument, or index. Three normative rules follow from that:
//   - Claim A: applying vpi_get_value() to such an expression shall fully
//     evaluate it together with its side effects.
//   - Claim B: it shall be an error to ask for a property or relation of an
//     expression when the value or handle cannot be determined without
//     evaluating an expression with side effects (Example 1: the vpiSize of a
//     function call that cannot be sized without calling it).
//   - Claim C: it shall be an error to apply vpi_put_value() to an object when
//     any of its index expressions has side effects (Example 2: my_array[i++]).
// The fixture installs a private context as the global one so the public
// vpi_get/vpi_get_value/vpi_put_value/vpi_handle entry points run their real
// dispatch and so vpi_chk_error() observes the recorded error, exactly as a PLI
// program would.
class ExpressionsWithSideEffects : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
};

// Claim A: applying vpi_get_value() to an expression with side effects fully
// evaluates the expression together with its side effects. The evaluation, and
// therefore the side effect, is observed through the per-expression count the
// read bumps; a second read evaluates the side effect again.
TEST_F(ExpressionsWithSideEffects, GetValueEvaluatesTheSideEffect) {
  VpiObject call;
  call.type = vpiFuncCall;  // e.g. ename(e), whose call mutates state
  call.has_side_effects = true;

  s_vpi_value value = {};
  value.format = vpiIntVal;

  vpi_get_value(&call, &value);
  EXPECT_EQ(call.side_effect_count, 1);

  vpi_get_value(&call, &value);
  EXPECT_EQ(call.side_effect_count, 2);
}

// Claim A (boundary): the full evaluation is the side effect's, not every
// read's. An expression with no side effects is read without any such
// evaluation, so its count stays at zero.
TEST_F(ExpressionsWithSideEffects,
       GetValueOnPlainExpressionEvaluatesNoSideEffect) {
  VpiObject expr;
  expr.type = vpiOperation;  // a plain operation, no side effects

  s_vpi_value value = {};
  value.format = vpiIntVal;

  vpi_get_value(&expr, &value);
  EXPECT_EQ(expr.side_effect_count, 0);
  EXPECT_FALSE(VpiExpressionHasSideEffects(&expr));
}

// Claim B (Example 1): asking for a property of an expression whose value
// cannot be determined without evaluating a side-effecting expression - such as
// the vpiSize of the function call ename(e) - is an error. vpi_get() refuses
// the query, records the error, and returns vpiUndefined.
TEST_F(ExpressionsWithSideEffects, GetPropertyNeedingSideEffectEvalIsAnError) {
  VpiObject call;
  call.type = vpiFuncCall;
  call.property_needs_side_effect_eval = true;

  EXPECT_EQ(vpi_get(vpiSize, &call), vpiUndefined);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  // The side effect was not triggered: the query was refused, not evaluated.
  EXPECT_EQ(call.side_effect_count, 0);
}

// Claim B (carve-out): the object's kind never requires evaluation, so vpiType
// remains answerable structurally on the very same expression - it returns the
// type and records no error.
TEST_F(ExpressionsWithSideEffects, GetTypeIsAllowedOnSuchAnExpression) {
  VpiObject call;
  call.type = vpiFuncCall;
  call.property_needs_side_effect_eval = true;

  EXPECT_EQ(vpi_get(vpiType, &call), vpiFuncCall);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

// Claim B (relation): the rule covers handles as well as values. Traversing a
// relation from an expression whose related handle cannot be determined without
// evaluating a side-effecting expression is an error: vpi_handle() refuses it,
// records the error, and returns a null handle.
TEST_F(ExpressionsWithSideEffects,
       HandleRelationNeedingSideEffectEvalIsAnError) {
  VpiObject call;
  call.type = vpiFuncCall;
  call.property_needs_side_effect_eval = true;

  EXPECT_EQ(vpi_handle(vpiExpr, &call), nullptr);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
}

// Claim C (Example 2): applying vpi_put_value() to an object one of whose index
// expressions has side effects - my_array[i++] - is an error. The write is
// rejected before any value is stored: it returns NULL and records the error.
TEST_F(ExpressionsWithSideEffects, PutValueWithSideEffectingIndexIsAnError) {
  VpiObject post_inc;  // the index expression i++
  post_inc.type = vpiOperation;
  post_inc.has_side_effects = true;

  VpiObject select;  // the target my_array[i++]
  select.type = vpiReg;
  select.index_expressions.push_back(&post_inc);

  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 1;

  EXPECT_EQ(vpi_put_value(&select, &value, nullptr, vpiNoDelay), nullptr);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  // The refused write never evaluated the side-effecting index expression.
  EXPECT_EQ(post_inc.side_effect_count, 0);
}

// Claim C (edge - "any of its index expressions"): the guard checks every index
// expression, not just the first. A multi-dimensional select whose leading
// index is side-effect-free but whose trailing index has side effects -
// my_array[2][--i] - is still rejected, exercising the loop past the clean
// index before it fires on the side-effecting one.
TEST_F(ExpressionsWithSideEffects,
       PutValueWithLaterSideEffectingIndexIsAnError) {
  VpiObject leading;  // the side-effect-free index 2
  leading.type = vpiConstant;

  VpiObject pre_dec;  // the trailing index expression --i
  pre_dec.type = vpiOperation;
  pre_dec.has_side_effects = true;

  VpiObject select;  // the target my_array[2][--i]
  select.type = vpiReg;
  select.index_expressions.push_back(&leading);
  select.index_expressions.push_back(&pre_dec);

  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 1;

  EXPECT_EQ(vpi_put_value(&select, &value, nullptr, vpiNoDelay), nullptr);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(pre_dec.side_effect_count, 0);
}

// Claim C (boundary): the restriction is on side-effecting index expressions
// only. An index expression without side effects - my_array[2] - does not trip
// the §37.3.5 guard, so vpi_put_value() records no error from it (the target
// here carries no storage, so the write simply stops with no error).
TEST_F(ExpressionsWithSideEffects, PutValueWithPlainIndexIsNotRefused) {
  VpiObject constant;  // the index expression 2
  constant.type = vpiConstant;

  VpiObject select;  // the target my_array[2]
  select.type = vpiReg;
  select.index_expressions.push_back(&constant);

  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 1;

  vpi_put_value(&select, &value, nullptr, vpiNoDelay);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

}  // namespace
}  // namespace delta
