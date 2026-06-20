#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.31 Class definition: the VPI object model for a class defn. The figure's
// structural relations (to variables, named events, parameters, the internal
// scope, the class typespec) and the simple properties (vpiName, vpiVirtual,
// vpiAutomatic) are served by the generic object-model machinery, so the tests
// below observe the rules this clause's own Details define and that need
// dedicated production code:
//   - Detail 1: the vpiMethods iteration returns the class's methods (tasks and
//     functions) but omits implicit built-in methods carrying no declaration.
//   - Detail 2: vpi_get_value()/vpi_put_value() are not allowed for variable
//   and
//     event handles obtained from a class defn handle.
//   - Detail 3: the vpiConstraint iteration returns only normal constraints,
//   not
//     inline constraints.
//   - Detail 5: the vpiDerivedClasses iteration returns the derived class
//   defns.
//   - Detail 6: the vpiArgument iteration from an extends object returns the
//     expressions used for constructor chaining.

// The fixture installs a context so the public vpi_iterate/vpi_scan/
// vpi_get_value/vpi_put_value entry points run their real dispatch and so
// vpi_chk_error() reports the errors the value routines record.
class ClassDefinition : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

std::vector<vpiHandle> ScanAll(vpiHandle it) {
  std::vector<vpiHandle> seen;
  if (!it) return seen;
  while (vpiHandle h = vpi_scan(it)) seen.push_back(h);
  return seen;
}

// D1: a class defn's vpiMethods iteration collects its method objects - the
// tasks and functions declared as class items - and omits an implicit built-in
// method (one provided with no explicit declaration). A method that is
// explicitly declared is reported whether or not it is built-in, and a
// non-method child (here a variables node) is not a method and never appears.
TEST_F(ClassDefinition, ClassMethodsIterationExcludesImplicitBuiltins) {
  VpiObject declared_func;
  declared_func.type = vpiFunction;
  VpiObject implicit_builtin;
  implicit_builtin.type = vpiFunction;
  implicit_builtin.implicit_builtin_method = true;  // dropped
  VpiObject declared_task;
  declared_task.type = vpiTask;
  VpiObject member_var;
  member_var.type = vpiVariables;  // not a method

  VpiObject class_defn;
  class_defn.type = vpiClassDefn;
  class_defn.children = {&declared_func, &member_var, &implicit_builtin,
                         &declared_task};

  vpiHandle it = vpi_iterate(vpiMethods, &class_defn);
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen = ScanAll(it);

  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], &declared_func);
  EXPECT_EQ(seen[1], &declared_task);
}

// D2: vpi_get_value() and vpi_put_value() are not allowed for a variable or
// event handle obtained from a class defn handle. Both a variable member and a
// named event member are refused by both routines: an error is recorded and a
// get leaves the caller's value buffer untouched.
TEST_F(ClassDefinition, ValueRoutinesDeniedForClassDefnMembers) {
  VpiObject class_defn;
  class_defn.type = vpiClassDefn;

  VpiObject member_var;
  member_var.type = vpiLogicVar;
  member_var.parent = &class_defn;
  VpiObject member_event;
  member_event.type = vpiNamedEvent;
  member_event.parent = &class_defn;

  for (VpiObject* member : {&member_var, &member_event}) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = 0x5eed;  // sentinel the get must not overwrite

    vpi_get_value(member, &value);
    SVpiErrorInfo get_info = {};
    EXPECT_EQ(VpiChkErrorC(&get_info), vpiError)
        << "get, type " << member->type;
    EXPECT_EQ(value.value.integer, 0x5eed) << "get, type " << member->type;

    vpiHandle ret = vpi_put_value(member, &value, nullptr, vpiNoDelay);
    EXPECT_EQ(ret, nullptr) << "put, type " << member->type;
    SVpiErrorInfo put_info = {};
    EXPECT_EQ(VpiChkErrorC(&put_info), vpiError)
        << "put, type " << member->type;
  }
}

// D2 scope: the restriction names handles obtained from a class defn handle.
// The same variable kind reached from a non-class-defn parent (here a module)
// is an ordinary variable, so neither value routine refuses it on §37.31's
// account. Both routines carry an independent guard whose parent-type arm must
// let it pass.
TEST_F(ClassDefinition, ValueRestrictionScopedToClassDefnParent) {
  VpiObject module;
  module.type = kVpiModule;

  VpiObject free_var;
  free_var.type = vpiLogicVar;
  free_var.parent = &module;

  s_vpi_value value = {};
  value.format = vpiIntVal;

  vpi_get_value(&free_var, &value);
  SVpiErrorInfo get_info = {};
  EXPECT_EQ(VpiChkErrorC(&get_info), 0);

  vpi_put_value(&free_var, &value, nullptr, vpiNoDelay);
  SVpiErrorInfo put_info = {};
  EXPECT_EQ(VpiChkErrorC(&put_info), 0);
}

// D2 scope: the restriction names variable and event handles specifically. A
// non-value member reached from a class defn handle - here a constraint - is
// not a variable or event, so the guard's type-membership arm must let it
// through and neither value routine refuses it on §37.31's account. This
// exercises the arm complementary to the denial test, which the module-parent
// test does not.
TEST_F(ClassDefinition, ValueRestrictionAppliesOnlyToVariableAndEventMembers) {
  VpiObject class_defn;
  class_defn.type = vpiClassDefn;

  VpiObject member_constraint;
  member_constraint.type = vpiConstraint;  // not a variable or event
  member_constraint.parent = &class_defn;

  s_vpi_value value = {};
  value.format = vpiIntVal;

  vpi_get_value(&member_constraint, &value);
  SVpiErrorInfo get_info = {};
  EXPECT_EQ(VpiChkErrorC(&get_info), 0);

  vpi_put_value(&member_constraint, &value, nullptr, vpiNoDelay);
  SVpiErrorInfo put_info = {};
  EXPECT_EQ(VpiChkErrorC(&put_info), 0);
}

// D3: a class defn's vpiConstraint iteration returns only normal constraints,
// in declaration order, and leaves out an inline constraint that sits among
// them.
TEST_F(ClassDefinition, ConstraintIterationExcludesInlineConstraints) {
  VpiObject normal_a;
  normal_a.type = vpiConstraint;
  VpiObject inline_c;
  inline_c.type = vpiConstraint;
  inline_c.inline_constraint = true;  // dropped
  VpiObject normal_b;
  normal_b.type = vpiConstraint;

  VpiObject class_defn;
  class_defn.type = vpiClassDefn;
  class_defn.children = {&normal_a, &inline_c, &normal_b};

  vpiHandle it = vpi_iterate(vpiConstraint, &class_defn);
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen = ScanAll(it);

  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], &normal_a);
  EXPECT_EQ(seen[1], &normal_b);
}

// D5: a class defn's vpiDerivedClasses iteration returns the class defns
// derived from it. The targets are class-defn objects, so a child of any other
// kind (here a constraint) is not reported.
TEST_F(ClassDefinition, DerivedClassesIterationReturnsDerivedClassDefns) {
  VpiObject derived_a;
  derived_a.type = vpiClassDefn;
  VpiObject derived_b;
  derived_b.type = vpiClassDefn;
  VpiObject not_a_class;
  not_a_class.type = vpiConstraint;

  VpiObject base;
  base.type = vpiClassDefn;
  base.children = {&derived_a, &not_a_class, &derived_b};

  vpiHandle it = vpi_iterate(vpiDerivedClasses, &base);
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen = ScanAll(it);

  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], &derived_a);
  EXPECT_EQ(seen[1], &derived_b);
}

// D6: the vpiArgument iteration from an extends object returns the expressions
// supplied for constructor chaining (8.17). The targets are expressions, so a
// child of a non-expression kind (here a parameter) is not reported.
TEST_F(ClassDefinition, ExtendsArgumentIterationReturnsChainingExpressions) {
  VpiObject arg_a;
  arg_a.type = vpiConstant;
  VpiObject arg_b;
  arg_b.type = vpiRefObj;
  VpiObject not_an_expr;
  not_an_expr.type = vpiParameter;

  VpiObject extends;
  extends.type = vpiExtends;
  extends.children = {&arg_a, &not_an_expr, &arg_b};

  vpiHandle it = vpi_iterate(vpiArgument, &extends);
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen = ScanAll(it);

  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], &arg_a);
  EXPECT_EQ(seen[1], &arg_b);
}

}  // namespace
}  // namespace delta
