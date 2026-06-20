#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.28 Parameter, spec param, def param, param assign: the VPI object model
// for parameters (vpiParameter), type parameters (vpiTypeParameter), def
// params, and param assigns (vpiParamAssign). These tests observe the
// production code that applies the clause's five numbered "Details":
//   - Detail 1: vpi_get_value() of a value parameter returns its value (served
//   by
//     §38.34's reader over the parameter's stored value).
//   - Detail 2: vpiTypespec of a type parameter returns the typespec it has at
//   the
//     end of elaboration, without resolving typedef aliases.
//   - Detail 3: vpiExpr of a parameter returns its default (a value parameter's
//     default expression, a type parameter's default typespec).
//   - Detail 4: vpiLhs of a param assign returns the overridden parameter.
//   - Detail 5: a value parameter declared without an explicit range reports a
//     null handle for vpiLeftRange and vpiRightRange.
// together with the figure's vpiLocalParam / vpiConnByName Boolean properties.

// The fixture installs a context so the public vpi_get / vpi_get_value /
// vpi_handle entry points run their real dispatch over the test objects.
class Parameter : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Figure properties: a parameter reports vpiLocalParam, and a param assign
// reports vpiConnByName, each as a Boolean served through the public vpi_get
// dispatch.
TEST_F(Parameter, LocalParamAndConnByNameProperties) {
  VpiObject local_param;
  local_param.type = vpiParameter;
  local_param.local_param = true;
  EXPECT_EQ(vpi_get(vpiLocalParam, &local_param), 1);

  VpiObject plain_param;
  plain_param.type = vpiParameter;  // not a localparam
  EXPECT_EQ(vpi_get(vpiLocalParam, &plain_param), 0);

  VpiObject by_name;
  by_name.type = vpiParamAssign;
  by_name.conn_by_name = true;
  EXPECT_EQ(vpi_get(vpiConnByName, &by_name), 1);

  VpiObject by_position;
  by_position.type = vpiParamAssign;  // connects by position
  EXPECT_EQ(vpi_get(vpiConnByName, &by_position), 0);
}

// D1: vpi_get_value() of a value parameter returns the value the parameter
// holds. The reader is §38.34's; this observes it serving a vpiParameter
// object.
TEST_F(Parameter, ValueParameterValueIsReadable) {
  Arena arena;
  Variable backing;
  backing.value = MakeLogic4VecVal(arena, 32, 0xABCDu);

  VpiObject param;
  param.type = vpiParameter;
  param.var = &backing;

  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(&param, &value);
  EXPECT_EQ(value.value.integer, 0xABCD);
}

// D2: vpiTypespec of a type parameter returns the typespec it resolved to,
// handed back without following any typedef alias. The recorded typespec is
// itself an alias whose underlying type is reachable as a child; the relation
// returns the alias, not the resolved underlying type.
TEST_F(Parameter, TypeParameterTypespecReturnedWithoutAliasResolution) {
  VpiObject resolved_ts;  // what the alias ultimately denotes
  resolved_ts.type = vpiTypespec;

  VpiObject alias_ts;  // a typedef-alias typespec referencing the resolved type
  alias_ts.type = vpiTypespec;
  alias_ts.children = {&resolved_ts};

  VpiObject
      default_ts;  // the type parameter's default typespec (the vpiExpr end)
  default_ts.type = vpiTypespec;

  VpiObject type_param;
  type_param.type = vpiTypeParameter;
  type_param.param_typespec = &alias_ts;
  type_param.param_default = &default_ts;

  // The alias is returned as-is, not resolved to its underlying type.
  EXPECT_EQ(VpiTypeParameterTypespec(&type_param), &alias_ts);
  EXPECT_EQ(vpi_handle(vpiTypespec, &type_param), &alias_ts);
  EXPECT_NE(vpi_handle(vpiTypespec, &type_param), &resolved_ts);

  // vpiTypespec (detail 2) and vpiExpr (detail 3) are distinct relations
  // reaching distinct typespecs.
  EXPECT_EQ(vpi_handle(vpiExpr, &type_param), &default_ts);
}

// D2 edge: the typespec helper speaks only for a type parameter. A value
// parameter's vpiTypespec is the generic child relation, not detail 2, so the
// helper returns null for it (and for a null handle).
TEST_F(Parameter, TypespecHelperOnlyForTypeParameter) {
  VpiObject ts;
  ts.type = vpiTypespec;

  VpiObject value_param;
  value_param.type = vpiParameter;
  value_param.children = {&ts};

  EXPECT_EQ(VpiTypeParameterTypespec(&value_param), nullptr);
  EXPECT_EQ(VpiTypeParameterTypespec(nullptr), nullptr);
  // The generic walk still serves a value parameter's vpiTypespec child.
  EXPECT_EQ(vpi_handle(vpiTypespec, &value_param), &ts);
}

// D3: vpiExpr of a value parameter reaches its default value expression.
TEST_F(Parameter, ValueParameterExprReachesDefaultExpression) {
  VpiObject default_expr;
  default_expr.type =
      vpiOperation;  // a concrete expr kind, not literally vpiExpr

  VpiObject param;
  param.type = vpiParameter;
  param.param_default = &default_expr;

  EXPECT_EQ(VpiParameterDefaultExpr(&param), &default_expr);
  EXPECT_EQ(vpi_handle(vpiExpr, &param), &default_expr);
}

// D3 edge: a parameter carrying no default reports null for vpiExpr, and the
// helper speaks only for parameter kinds.
TEST_F(Parameter, ParameterExprIsNullWithoutDefault) {
  VpiObject param;
  param.type = vpiParameter;  // no default recorded
  EXPECT_EQ(VpiParameterDefaultExpr(&param), nullptr);
  EXPECT_EQ(vpi_handle(vpiExpr, &param), nullptr);

  VpiObject other;
  other.type = vpiModule;
  EXPECT_EQ(VpiParameterDefaultExpr(&other), nullptr);
  EXPECT_EQ(VpiParameterDefaultExpr(nullptr), nullptr);
}

// D4: vpiLhs of a param assign reaches the overridden parameter - the value
// parameter for a value override and the type parameter for a type override.
TEST_F(Parameter, ParamAssignLhsReachesOverriddenParameter) {
  VpiObject overridden_value;
  overridden_value.type = vpiParameter;
  VpiObject value_rhs;
  value_rhs.type = vpiOperation;

  VpiObject value_assign;
  value_assign.type = vpiParamAssign;
  value_assign.children = {&value_rhs, &overridden_value};
  EXPECT_EQ(VpiParamAssignLhs(&value_assign), &overridden_value);
  EXPECT_EQ(vpi_handle(vpiLhs, &value_assign), &overridden_value);

  VpiObject overridden_type;
  overridden_type.type = vpiTypeParameter;
  VpiObject type_assign;
  type_assign.type = vpiParamAssign;
  type_assign.children = {&overridden_type};
  EXPECT_EQ(vpi_handle(vpiLhs, &type_assign), &overridden_type);
}

// D4 edge: a param assign with no parameter-kind child reaches no lhs, and the
// helper speaks only for a param assign.
TEST_F(Parameter, ParamAssignLhsIsNullWithoutParameterChild) {
  VpiObject rhs;
  rhs.type = vpiOperation;

  VpiObject assign;
  assign.type = vpiParamAssign;
  assign.children = {&rhs};  // only an rhs expression, no overridden parameter
  EXPECT_EQ(VpiParamAssignLhs(&assign), nullptr);
  EXPECT_EQ(vpi_handle(vpiLhs, &assign), nullptr);

  VpiObject not_assign;
  not_assign.type = vpiParameter;
  EXPECT_EQ(VpiParamAssignLhs(&not_assign), nullptr);
}

// D5: a value parameter declared without an explicit range reports a null
// handle for both vpiLeftRange and vpiRightRange.
TEST_F(Parameter, UnrangedValueParameterReportsNullRanges) {
  VpiObject param;
  param.type = vpiParameter;  // explicit_param_range stays false
  EXPECT_EQ(VpiParameterLeftRange(&param), nullptr);
  EXPECT_EQ(VpiParameterRightRange(&param), nullptr);
  EXPECT_EQ(vpi_handle(vpiLeftRange, &param), nullptr);
  EXPECT_EQ(vpi_handle(vpiRightRange, &param), nullptr);
}

// D5: a value parameter with an explicit range reaches its range-bound
// expressions; the range helpers speak only for a parameter.
TEST_F(Parameter, RangedValueParameterReachesRangeBounds) {
  VpiObject left_bound;
  left_bound.type = vpiConstant;
  VpiObject right_bound;
  right_bound.type = vpiConstant;

  VpiObject param;
  param.type = vpiParameter;
  param.explicit_param_range = true;
  param.param_left_range = &left_bound;
  param.param_right_range = &right_bound;

  EXPECT_EQ(vpi_handle(vpiLeftRange, &param), &left_bound);
  EXPECT_EQ(vpi_handle(vpiRightRange, &param), &right_bound);

  VpiObject other;
  other.type = vpiNet;
  other.explicit_param_range = true;
  EXPECT_EQ(VpiParameterLeftRange(&other), nullptr);
  EXPECT_EQ(VpiParameterRightRange(nullptr), nullptr);
}

}  // namespace
}  // namespace delta
