#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <tuple>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class Parameter : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(Parameter, LocalParamAndConnByNameProperties) {
  VpiObject local_param;
  local_param.type = vpiParameter;
  local_param.local_param = true;
  EXPECT_EQ(vpi_get(vpiLocalParam, VpiHandleOf(&local_param)), 1);

  VpiObject plain_param;
  plain_param.type = vpiParameter;
  EXPECT_EQ(vpi_get(vpiLocalParam, VpiHandleOf(&plain_param)), 0);

  VpiObject by_name;
  by_name.type = vpiParamAssign;
  by_name.conn_by_name = true;
  EXPECT_EQ(vpi_get(vpiConnByName, VpiHandleOf(&by_name)), 1);

  VpiObject by_position;
  by_position.type = vpiParamAssign;
  EXPECT_EQ(vpi_get(vpiConnByName, VpiHandleOf(&by_position)), 0);
}

TEST_F(Parameter, LocalParamPropertyAppliesToTypeParameter) {
  VpiObject local_type_param;
  local_type_param.type = vpiTypeParameter;
  local_type_param.local_param = true;
  EXPECT_EQ(vpi_get(vpiLocalParam, VpiHandleOf(&local_type_param)), 1);

  VpiObject plain_type_param;
  plain_type_param.type = vpiTypeParameter;
  EXPECT_EQ(vpi_get(vpiLocalParam, VpiHandleOf(&plain_type_param)), 0);
}

TEST_F(Parameter, ValueParameterValueIsReadable) {
  Arena arena;
  Variable backing;
  backing.value = MakeLogic4VecVal(arena, 32, 0xABCDu);

  VpiObject param;
  param.type = vpiParameter;
  param.var = &backing;

  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(VpiHandleOf(&param), &value);
  EXPECT_EQ(value.value.integer, 0xABCD);
}

TEST_F(Parameter, TypeParameterTypespecReturnedWithoutAliasResolution) {
  VpiObject resolved_ts;
  resolved_ts.type = vpiTypespec;

  VpiObject alias_ts;
  alias_ts.type = vpiTypespec;
  alias_ts.children = {&resolved_ts};

  VpiObject default_ts;
  default_ts.type = vpiTypespec;

  VpiObject type_param;
  type_param.type = vpiTypeParameter;
  type_param.param_typespec = &alias_ts;
  type_param.param_default = &default_ts;

  EXPECT_EQ(VpiTypeParameterTypespec(&type_param), &alias_ts);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTypespec, VpiHandleOf(&type_param))),
            &alias_ts);
  EXPECT_NE(VpiObjectOf(vpi_handle(vpiTypespec, VpiHandleOf(&type_param))),
            &resolved_ts);

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&type_param))),
            &default_ts);
}

TEST_F(Parameter, TypespecHelperOnlyForTypeParameter) {
  VpiObject ts;
  ts.type = vpiTypespec;

  VpiObject value_param;
  value_param.type = vpiParameter;
  value_param.children = {&ts};

  EXPECT_EQ(VpiTypeParameterTypespec(&value_param), nullptr);
  EXPECT_EQ(VpiTypeParameterTypespec(nullptr), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTypespec, VpiHandleOf(&value_param))),
            &ts);
}

TEST_F(Parameter, ValueParameterExprReachesDefaultExpression) {
  VpiObject default_expr;
  default_expr.type = vpiOperation;

  VpiObject param;
  param.type = vpiParameter;
  param.param_default = &default_expr;

  EXPECT_EQ(VpiParameterDefaultExpr(&param), &default_expr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&param))),
            &default_expr);
}

TEST_F(Parameter, ParameterExprIsNullWithoutDefault) {
  VpiObject param;
  param.type = vpiParameter;
  EXPECT_EQ(VpiParameterDefaultExpr(&param), nullptr);
  EXPECT_EQ(vpi_handle(vpiExpr, VpiHandleOf(&param)), nullptr);

  VpiObject other;
  other.type = vpiModule;
  EXPECT_EQ(VpiParameterDefaultExpr(&other), nullptr);
  EXPECT_EQ(VpiParameterDefaultExpr(nullptr), nullptr);
}

TEST_F(Parameter, ParamAssignLhsReachesOverriddenParameter) {
  VpiObject overridden_value;
  overridden_value.type = vpiParameter;
  VpiObject value_rhs;
  value_rhs.type = vpiOperation;

  VpiObject value_assign;
  value_assign.type = vpiParamAssign;
  value_assign.children = {&value_rhs, &overridden_value};
  EXPECT_EQ(VpiParamAssignLhs(&value_assign), &overridden_value);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, VpiHandleOf(&value_assign))),
            &overridden_value);

  VpiObject overridden_type;
  overridden_type.type = vpiTypeParameter;
  VpiObject type_assign;
  type_assign.type = vpiParamAssign;
  type_assign.children = {&overridden_type};
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, VpiHandleOf(&type_assign))),
            &overridden_type);
}

TEST_F(Parameter, ParamAssignLhsIsNullWithoutParameterChild) {
  VpiObject rhs;
  rhs.type = vpiOperation;

  VpiObject assign;
  assign.type = vpiParamAssign;
  assign.children = {&rhs};
  EXPECT_EQ(VpiParamAssignLhs(&assign), nullptr);
  EXPECT_EQ(vpi_handle(vpiLhs, VpiHandleOf(&assign)), nullptr);

  VpiObject not_assign;
  not_assign.type = vpiParameter;
  EXPECT_EQ(VpiParamAssignLhs(&not_assign), nullptr);
}

TEST_F(Parameter, UnrangedValueParameterReportsNullRanges) {
  VpiObject param;
  param.type = vpiParameter;
  EXPECT_EQ(VpiParameterLeftRange(&param), nullptr);
  EXPECT_EQ(VpiParameterRightRange(&param), nullptr);
  EXPECT_EQ(vpi_handle(vpiLeftRange, VpiHandleOf(&param)), nullptr);
  EXPECT_EQ(vpi_handle(vpiRightRange, VpiHandleOf(&param)), nullptr);
}

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

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLeftRange, VpiHandleOf(&param))),
            &left_bound);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRightRange, VpiHandleOf(&param))),
            &right_bound);

  VpiObject other;
  other.type = vpiNet;
  other.explicit_param_range = true;
  EXPECT_EQ(VpiParameterLeftRange(&other), nullptr);
  EXPECT_EQ(VpiParameterRightRange(nullptr), nullptr);
}

class ParametersOfARun : public VpiDesignRun {};

constexpr const char* kParameters =
    "module top;\n"
    "  parameter int P = 5;\n"
    "  localparam int L = 7;\n"
    "  parameter type T = logic [3:0];\n"
    "endmodule\n";

vpiHandle ChildOf(int type, vpiHandle scope, std::string_view name) {
  vpiHandle it = vpi_iterate(type, scope);
  if (it == nullptr) return nullptr;
  while (vpiHandle obj = vpi_scan(it)) {
    if (vpi_get_str(vpiName, obj) == name) {
      vpi_free_object(it);
      return obj;
    }
  }
  return nullptr;
}

TEST_F(ParametersOfARun, AModulesParametersAndTypeParametersAreParameters) {
  Run(kParameters);
  EXPECT_EQ(NamesOf(vpiParameter, vpi_handle_by_name(VpiText("top"), nullptr)),
            (std::vector<std::string>{"L", "P", "T"}));
}

TEST_F(ParametersOfARun, ALocalparamIsALocalParam) {
  Run(kParameters);
  EXPECT_EQ(
      vpi_get(vpiLocalParam, vpi_handle_by_name(VpiText("top.L"), nullptr)), 1);
}

TEST_F(ParametersOfARun, AParameterIsNotALocalParam) {
  Run(kParameters);
  EXPECT_EQ(
      vpi_get(vpiLocalParam, vpi_handle_by_name(VpiText("top.P"), nullptr)), 0);
}

TEST_F(ParametersOfARun, AParametersValueIsRead) {
  Run(kParameters);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(vpi_handle_by_name(VpiText("top.P"), nullptr), &value);
  EXPECT_EQ(value.value.integer, 5);
}

TEST_F(ParametersOfARun, ATypeParameterIsATypeParameter) {
  Run(kParameters);
  EXPECT_NE(ChildOf(vpiTypeParameter,
                    vpi_handle_by_name(VpiText("top"), nullptr), "T"),
            nullptr);
}

vpiHandle TypespecOf(const char* scope, std::string_view name) {
  return vpi_handle(vpiTypespec,
                    ChildOf(vpiTypeParameter,
                            vpi_handle_by_name(VpiText(scope), nullptr), name));
}

constexpr const char* kTypeParameterTypes =
    "typedef enum {X, Y} ue_t;\n"
    "module c;\n"
    "  parameter type T = int;\n"
    "endmodule\n"
    "module d #(parameter type T = shortint);\n"
    "endmodule\n"
    "module e #(parameter type T = ue_t);\n"
    "endmodule\n"
    "module top;\n"
    "  typedef enum {A, B, C} e_t;\n"
    "  parameter type L = e_t;\n"
    "  parameter type U = ue_t;\n"
    "  c #(.T(ue_t)) u();\n"
    "  d v();\n"
    "  d #(.T(ue_t)) w();\n"
    "  e x();\n"
    "endmodule\n";

TEST_F(ParametersOfARun, ATypeParametersTypespecIsTheTypedefItNames) {
  Run(kTypeParameterTypes);
  EXPECT_STREQ(vpi_get_str(vpiName, TypespecOf("top", "L")), "e_t");
}

TEST_F(ParametersOfARun, ATypeParametersTypespecIsTheUnitsTypedefItNames) {
  Run(kTypeParameterTypes);
  EXPECT_STREQ(vpi_get_str(vpiName, TypespecOf("top", "U")), "ue_t");
}

TEST_F(ParametersOfARun,
       AnOverriddenTypeParametersTypespecIsTheTypeItWasGiven) {
  Run(kTypeParameterTypes);
  vpiHandle typespec = TypespecOf("top.u", "T");
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiEnumTypespec);
  EXPECT_STREQ(vpi_get_str(vpiName, typespec), "ue_t");
}

TEST_F(ParametersOfARun, ATypeParametersTypespecIsOfItsTypesKind) {
  Run(kParameters);
  EXPECT_EQ(vpi_get(vpiType, TypespecOf("top", "T")), vpiLogicTypespec);
}

TEST_F(ParametersOfARun, AParameterPortsTypespecIsOfItsTypesKind) {
  Run(kTypeParameterTypes);
  EXPECT_EQ(vpi_get(vpiType, TypespecOf("top.v", "T")), vpiShortIntTypespec);
}

TEST_F(ParametersOfARun,
       AnOverriddenParameterPortsTypespecIsTheTypedefItNames) {
  Run(kTypeParameterTypes);
  vpiHandle typespec = TypespecOf("top.w", "T");
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiEnumTypespec);
  EXPECT_STREQ(vpi_get_str(vpiName, typespec), "ue_t");
}

TEST_F(ParametersOfARun, AParameterPortsTypespecIsTheTypedefItsDefaultNames) {
  Run(kTypeParameterTypes);
  EXPECT_STREQ(vpi_get_str(vpiName, TypespecOf("top.x", "T")), "ue_t");
}

constexpr const char* kPackageParameters =
    "package pkg;\n"
    "  parameter int P = 5;\n"
    "  localparam int L = 7;\n"
    "  parameter type T = logic [3:0];\n"
    "endpackage\n"
    "module top; endmodule\n";

TEST_F(ParametersOfARun, APackagesParametersAndTypeParametersAreParameters) {
  Run(kPackageParameters);
  EXPECT_EQ(NamesOf(vpiParameter, vpi_handle_by_name(VpiText("pkg"), nullptr)),
            (std::vector<std::string>{"L", "P", "T"}));
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_name(VpiText("pkg::P"), nullptr)),
            vpiParameter);
}

TEST_F(ParametersOfARun, APackagesParameterIsALocalParam) {
  Run(kPackageParameters);
  EXPECT_EQ(
      vpi_get(vpiLocalParam, vpi_handle_by_name(VpiText("pkg::P"), nullptr)),
      1);
}

TEST_F(ParametersOfARun, APackagesTypeParameterIsATypeParameter) {
  Run(kPackageParameters);
  vpiHandle type = ChildOf(vpiTypeParameter,
                           vpi_handle_by_name(VpiText("pkg"), nullptr), "T");
  ASSERT_NE(type, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, type), "pkg::T");
  EXPECT_EQ(vpi_get(vpiType, TypespecOf("pkg", "T")), vpiLogicTypespec);
}

TEST_F(Parameter, OnlyAGenvarReferenceInAGenScopeIsALocalParam) {
  VpiObject scope;
  scope.type = vpiGenScope;
  VpiObject var;
  var.type = vpiIntVar;
  var.parent = &scope;
  EXPECT_EQ(vpi_get(vpiLocalParam, VpiHandleOf(&var)), 0);
  VpiObject unbound;
  unbound.type = vpiRefObj;
  unbound.parent = &scope;
  EXPECT_EQ(vpi_get(vpiLocalParam, VpiHandleOf(&unbound)), 0);
}

TEST_F(Parameter, NoObjectOrAnotherKindHasNoLhsOrRange) {
  EXPECT_EQ(VpiParamAssignLhs(nullptr), nullptr);
  EXPECT_EQ(VpiParameterLeftRange(nullptr), nullptr);
  VpiObject constant;
  constant.type = vpiConstant;
  EXPECT_EQ(VpiParameterRightRange(&constant), nullptr);
}

int IntValueOf(vpiHandle obj) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = -1;
  if (obj != nullptr) vpi_get_value(obj, &value);
  return value.value.integer;
}

int KindOf(int relation, vpiHandle ref) {
  vpiHandle reached = ref == nullptr ? nullptr : vpi_handle(relation, ref);
  return reached == nullptr ? 0 : vpi_get(vpiType, reached);
}

constexpr const char* kDescribed =
    "module m #(parameter int W = 2, parameter type T = int) (); endmodule\n"
    "module top;\n"
    "  parameter int P = 5;\n"
    "  parameter logic [7:0] R = 8'h3c;\n"
    "  parameter real F = 1.5;\n"
    "  parameter string S = \"hi\";\n"
    "  parameter Q = 9;\n"
    "  parameter type D = byte;\n"
    "  m #(.W(4)) u();\n"
    "  m #(6) v();\n"
    "  if (1) begin : g\n"
    "    parameter type GT = bit;\n"
    "  end\n"
    "endmodule\n";

vpiHandle In(const char* scope, const char* name) {
  return ChildOf(vpiParameter, vpi_handle_by_name(VpiText(scope), nullptr),
                 name);
}

TEST_F(ParametersOfARun, AValueParameterReportsItsConstType) {
  Run(kDescribed);
  EXPECT_EQ(vpi_get(vpiConstType, In("top", "P")), vpiIntConst);
  EXPECT_EQ(vpi_get(vpiConstType, In("top", "F")), vpiRealConst);
  EXPECT_EQ(vpi_get(vpiConstType, In("top", "S")), vpiStringConst);
}

TEST_F(ParametersOfARun, AParameterWithARangeReachesItsBounds) {
  Run(kDescribed);
  EXPECT_EQ(IntValueOf(vpi_handle(vpiLeftRange, In("top", "R"))), 7);
  EXPECT_EQ(IntValueOf(vpi_handle(vpiRightRange, In("top", "R"))), 0);
  EXPECT_EQ(vpi_handle(vpiLeftRange, In("top", "P")), nullptr);
}

TEST_F(ParametersOfARun, AParameterReachesItsDefault) {
  Run(kDescribed);
  EXPECT_EQ(IntValueOf(vpi_handle(vpiExpr, In("top", "P"))), 5);
  EXPECT_EQ(IntValueOf(vpi_handle(vpiExpr, In("top.u", "W"))), 2);
  EXPECT_EQ(KindOf(vpiExpr, In("top", "D")), vpiByteTypespec);
  EXPECT_EQ(KindOf(vpiExpr, In("top.u", "T")), vpiIntTypespec);
}

TEST_F(ParametersOfARun, AValueParameterReachesItsTypespec) {
  Run(kDescribed);
  EXPECT_EQ(KindOf(vpiTypespec, In("top", "P")), vpiIntTypespec);
  EXPECT_EQ(KindOf(vpiTypespec, In("top", "F")), vpiRealTypespec);
  EXPECT_EQ(KindOf(vpiTypespec, In("top", "S")), vpiStringTypespec);
  vpiHandle of_r = vpi_handle(vpiTypespec, In("top", "R"));
  ASSERT_NE(of_r, nullptr);
  EXPECT_EQ(vpi_get(vpiType, of_r), vpiLogicTypespec);
  vpiHandle ranges = vpi_iterate(vpiRange, of_r);
  ASSERT_NE(ranges, nullptr);
  EXPECT_EQ(IntValueOf(vpi_handle(vpiLeftRange, vpi_scan(ranges))), 7);
  vpiHandle of_q = vpi_handle(vpiTypespec, In("top", "Q"));
  ASSERT_NE(of_q, nullptr);
  EXPECT_EQ(vpi_get(vpiType, of_q), vpiLogicTypespec);
  EXPECT_NE(vpi_iterate(vpiRange, of_q), nullptr);
}

TEST_F(ParametersOfARun, AGenerateBlocksTypeParameterIsItsOwn) {
  Run(kDescribed);
  vpiHandle gt = In("top.g", "GT");
  ASSERT_NE(gt, nullptr);
  EXPECT_EQ(vpi_get(vpiType, gt), vpiTypeParameter);
  EXPECT_EQ(KindOf(vpiTypespec, gt), vpiBitTypespec);
}

TEST_F(ParametersOfARun, AnInstanceHoldsItsParamAssigns) {
  Run(kDescribed);
  for (const auto& [scope, value, by_name] :
       {std::tuple{"top.u", 4, 1}, std::tuple{"top.v", 6, 0}}) {
    vpiHandle it = vpi_iterate(vpiParamAssign,
                               vpi_handle_by_name(VpiText(scope), nullptr));
    ASSERT_NE(it, nullptr) << scope;
    vpiHandle assign = vpi_scan(it);
    ASSERT_NE(assign, nullptr) << scope;
    EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiLhs, assign)), "W");
    EXPECT_EQ(IntValueOf(vpi_handle(vpiRhs, assign)), value) << scope;
    EXPECT_EQ(vpi_get(vpiConnByName, assign), by_name) << scope;
  }
}

TEST_F(ParametersOfARun, ANestedModulesTypeParameterReachesItsDefault) {
  Run("module top;\n"
      "  module inner #(parameter type T = byte); endmodule\n"
      "  inner i();\n"
      "endmodule\n");
  EXPECT_EQ(KindOf(vpiExpr, In("top.i", "T")), vpiByteTypespec);
}

}  // namespace
}  // namespace delta
