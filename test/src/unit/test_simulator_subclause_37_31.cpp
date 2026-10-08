#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

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
  member_var.type = vpiLogicVar;  // not a method

  VpiObject class_defn;
  class_defn.type = vpiClassDefn;
  class_defn.children = {&declared_func, &member_var, &implicit_builtin,
                         &declared_task};

  vpiHandle it = vpi_iterate(vpiMethods, VpiHandleOf(&class_defn));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen = ScanAll(it);

  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &declared_func);
  EXPECT_EQ(VpiObjectOf(seen[1]), &declared_task);
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

    vpi_get_value(VpiHandleOf(member), &value);
    s_vpi_error_info get_info = {};
    EXPECT_EQ(vpi_chk_error(&get_info), vpiError)
        << "get, type " << member->type;
    EXPECT_EQ(value.value.integer, 0x5eed) << "get, type " << member->type;

    vpiHandle ret =
        vpi_put_value(VpiHandleOf(member), &value, nullptr, vpiNoDelay);
    EXPECT_EQ(ret, nullptr) << "put, type " << member->type;
    s_vpi_error_info put_info = {};
    EXPECT_EQ(vpi_chk_error(&put_info), vpiError)
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

  vpi_get_value(VpiHandleOf(&free_var), &value);
  s_vpi_error_info get_info = {};
  EXPECT_EQ(vpi_chk_error(&get_info), 0);

  vpi_put_value(VpiHandleOf(&free_var), &value, nullptr, vpiNoDelay);
  s_vpi_error_info put_info = {};
  EXPECT_EQ(vpi_chk_error(&put_info), 0);
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

  vpi_get_value(VpiHandleOf(&member_constraint), &value);
  s_vpi_error_info get_info = {};
  EXPECT_EQ(vpi_chk_error(&get_info), 0);

  vpi_put_value(VpiHandleOf(&member_constraint), &value, nullptr, vpiNoDelay);
  s_vpi_error_info put_info = {};
  EXPECT_EQ(vpi_chk_error(&put_info), 0);
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

  vpiHandle it = vpi_iterate(vpiConstraint, VpiHandleOf(&class_defn));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen = ScanAll(it);

  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &normal_a);
  EXPECT_EQ(VpiObjectOf(seen[1]), &normal_b);
}

// D5: a class defn's vpiDerivedClasses iteration returns the class defns
// derived from it, which the base holds apart from its children: a class defn
// among its children (here one nested in it) is not derived from it.
TEST_F(ClassDefinition, DerivedClassesIterationReturnsDerivedClassDefns) {
  VpiObject derived_a;
  derived_a.type = vpiClassDefn;
  VpiObject derived_b;
  derived_b.type = vpiClassDefn;
  VpiObject nested;
  nested.type = vpiClassDefn;

  VpiObject base;
  base.type = vpiClassDefn;
  base.children = {&nested};
  base.derived_classes = {&derived_a, &derived_b};

  vpiHandle it = vpi_iterate(vpiDerivedClasses, VpiHandleOf(&base));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen = ScanAll(it);

  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &derived_a);
  EXPECT_EQ(VpiObjectOf(seen[1]), &derived_b);
}

// D7: a class defn's vpiParameter iteration returns both the parameters of the
// class's parameter port list and those declared as class items in the body,
// and vpiLocalParam is TRUE only for the body-declared ones. The two parameters
// are ordinary vpiParameter children, so the generic child walk reports both in
// declaration order; the per-parameter local_param flag is what distinguishes
// them, observed through vpi_get(vpiLocalParam). A non-parameter child (here a
// constraint) is not a parameter and never appears.
TEST_F(ClassDefinition, ParameterIterationReportsPortAndBodyWithLocalParam) {
  VpiObject port_param;  // declared in the parameter port list
  port_param.type = vpiParameter;
  port_param.local_param = false;
  VpiObject not_a_param;
  not_a_param.type = vpiConstraint;
  VpiObject body_param;  // declared as a class item in the body
  body_param.type = vpiParameter;
  body_param.local_param = true;

  VpiObject class_defn;
  class_defn.type = vpiClassDefn;
  class_defn.children = {&port_param, &not_a_param, &body_param};

  vpiHandle it = vpi_iterate(vpiParameter, VpiHandleOf(&class_defn));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen = ScanAll(it);

  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &port_param);
  EXPECT_EQ(VpiObjectOf(seen[1]), &body_param);

  // vpiLocalParam is FALSE for the port-list parameter and TRUE for the
  // body-declared one.
  EXPECT_EQ(vpi_get(vpiLocalParam, VpiHandleOf(&port_param)), 0);
  EXPECT_EQ(vpi_get(vpiLocalParam, VpiHandleOf(&body_param)), 1);
}

// D6: the vpiArgument iteration from an extends object returns the expressions
// supplied for constructor chaining (8.17). The targets are expressions, so a
// child of a non-expression kind is not reported. The non-expression child is
// the class typespec the diagram draws the extends object reaching for its base
// class - the one other child an extends object of a design carries, and the
// one the argument iteration has to step over. A parameter stood here before,
// as a kind no expression scan would admit; §37.58 draws a parameter inside the
// `simple expr` class §37.59's `expr` groups, so it is an expression and the
// case it was written to make was made by an argument.
TEST_F(ClassDefinition, ExtendsArgumentIterationReturnsChainingExpressions) {
  VpiObject arg_a;
  arg_a.type = vpiConstant;
  VpiObject arg_b;
  arg_b.type = vpiRefObj;
  VpiObject not_an_expr;
  not_an_expr.type = vpiClassTypespec;

  VpiObject extends;
  extends.type = vpiExtends;
  extends.children = {&arg_a, &not_an_expr, &arg_b};

  vpiHandle it = vpi_iterate(vpiArgument, VpiHandleOf(&extends));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen = ScanAll(it);

  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &arg_a);
  EXPECT_EQ(VpiObjectOf(seen[1]), &arg_b);
}

// A design run with a PLI application registered, whose class definitions are
// read back from the model the run built.
class ClassDefinitionsOfARun : public VpiDesignRun {
 protected:
  // The class defn of `scope` named `name`, null for none.
  static vpiHandle DefnIn(vpiHandle scope, std::string_view name) {
    return Named(vpiClassDefn, scope, name);
  }
};

// §37.31: a class a module declares is a class defn of each of its instances,
// full-named under the instance...
TEST_F(ClassDefinitionsOfARun, AModuleClassIsAClassDefnOfItsInstance) {
  Run("module top; class Packet; endclass endmodule\n");
  EXPECT_EQ(NamesOf(vpiClassDefn, By("top")),
            std::vector<std::string>{"Packet"});
  vpiHandle defn = By("top.Packet");
  ASSERT_NE(defn, nullptr);
  EXPECT_EQ(vpi_get(vpiType, defn), vpiClassDefn);
  EXPECT_STREQ(vpi_get_str(vpiFullName, defn), "top.Packet");
}

// ...reporting whether it is virtual...
TEST_F(ClassDefinitionsOfARun, AVirtualClassReportsVpiVirtual) {
  Run("module top; virtual class Shape; endclass\n"
      "  class Square extends Shape; endclass endmodule\n");
  EXPECT_EQ(vpi_get(vpiVirtual, DefnIn(By("top"), "Shape")), 1);
  EXPECT_EQ(vpi_get(vpiVirtual, DefnIn(By("top"), "Square")), 0);
}

// ...a package's class is a class defn of the package...
TEST_F(ClassDefinitionsOfARun, APackageClassIsAClassDefnOfThePackage) {
  Run("package pkg; class Item; endclass endpackage\n"
      "module top; endmodule\n");
  vpiHandle defn = DefnIn(By("pkg"), "Item");
  ASSERT_NE(defn, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, defn), "pkg::Item");
}

// ...and the compilation unit's are reached with a NULL reference, which
// reaches no class an instance declares.
TEST_F(ClassDefinitionsOfARun, AUnitClassIsReachedWithANullReference) {
  Run("class Unit; endclass\n"
      "module top; class Packet; endclass endmodule\n");
  EXPECT_EQ(NamesOf(vpiClassDefn, nullptr), std::vector<std::string>{"Unit"});
  vpiHandle it = vpi_iterate(vpiClassDefn, nullptr);
  ASSERT_NE(it, nullptr);
  vpiHandle defn = vpi_scan(it);
  vpi_release_handle(it);
  EXPECT_STREQ(vpi_get_str(vpiFullName, defn), "$unit::Unit");
}

// Detail 6: a derived class reaches its base through its extends object, and
// the arguments its constructor chaining passes...
TEST_F(ClassDefinitionsOfARun, ADerivedClassReachesItsBaseThroughExtends) {
  Run("module top; class Base; function new(int n); endfunction endclass\n"
      "  class Derived extends Base(5); endclass endmodule\n");
  vpiHandle base = DefnIn(By("top"), "Base");
  vpiHandle extends = vpi_handle(vpiExtends, DefnIn(By("top"), "Derived"));
  ASSERT_NE(extends, nullptr);
  vpiHandle typespec = vpi_handle(vpiClassTypespec, extends);
  ASSERT_NE(typespec, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, typespec), "Base");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClassDefn, typespec)), VpiObjectOf(base));
  vpiHandle args = vpi_iterate(vpiArgument, extends);
  ASSERT_NE(args, nullptr);
  vpiHandle arg = vpi_scan(args);
  vpi_release_handle(args);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(arg, &value);
  EXPECT_EQ(value.value.integer, 5);
  EXPECT_EQ(vpi_handle(vpiExtends, base), nullptr);
}

// ...and detail 5: a base class iterates the classes derived from it.
TEST_F(ClassDefinitionsOfARun, ABaseClassIteratesItsDerivedClasses) {
  Run("module top; class Base; endclass class A extends Base; endclass\n"
      "  class B extends Base; endclass class C; endclass endmodule\n");
  EXPECT_EQ(NamesOf(vpiDerivedClasses, DefnIn(By("top"), "Base")),
            (std::vector<std::string>{"A", "B"}));
}

// ...which it holds apart from what it declares: neither an iteration of its
// class defns nor a name walked through it reaches one (#5045).
TEST_F(ClassDefinitionsOfARun, ABaseClassDeclaresNoClassDerivedFromIt) {
  Run("module top; class Base; endclass class A extends Base; endclass\n"
      "endmodule\n");
  EXPECT_TRUE(NamesOf(vpiClassDefn, DefnIn(By("top"), "Base")).empty());
  EXPECT_EQ(By("top.Base.A"), nullptr);
}

constexpr const char* kPacket =
    "module top; class Packet; static int Id; int len; local byte tag;\n"
    "  function int size(); return 4; endfunction\n"
    "  protected task run(); endtask endclass endmodule\n";

// Detail 1 (#5041): a class defn iterates its properties, static and
// automatic alike, each of the kind its type takes...
TEST_F(ClassDefinitionsOfARun, AClassDefnIteratesItsProperties) {
  Run(kPacket);
  vpiHandle defn = DefnIn(By("top"), "Packet");
  EXPECT_EQ(NamesOf(vpiVariables, defn),
            (std::vector<std::string>{"Id", "len", "tag"}));
  EXPECT_EQ(vpi_get(vpiType, Named(vpiVariables, defn, "tag")), vpiByteVar);
}

// ...a static one full-named through its class and reached by that name
// (§37.17 detail 25)...
TEST_F(ClassDefinitionsOfARun, AStaticPropertyIsNamedThroughItsClass) {
  Run(kPacket);
  vpiHandle id = By("top.Packet::Id");
  ASSERT_NE(id, nullptr);
  EXPECT_EQ(vpi_get(vpiType, id), vpiIntVar);
  EXPECT_STREQ(vpi_get_str(vpiFullName, id), "top.Packet::Id");
}

// ...each reporting the visibility it was declared with (§37.17 detail 24).
TEST_F(ClassDefinitionsOfARun, APropertyReportsItsVisibility) {
  Run(kPacket);
  vpiHandle defn = DefnIn(By("top"), "Packet");
  EXPECT_EQ(vpi_get(vpiVisibility, Named(vpiVariables, defn, "tag")),
            vpiLocalVis);
  EXPECT_EQ(vpi_get(vpiVisibility, Named(vpiVariables, defn, "len")),
            vpiPublicVis);
}

// Detail 1 (#5042): a class defn iterates its methods, each a method of the
// kind it was declared as, reporting its visibility (§37.41 details 4 and 5).
TEST_F(ClassDefinitionsOfARun, AClassDefnIteratesItsMethods) {
  Run(kPacket);
  vpiHandle defn = DefnIn(By("top"), "Packet");
  EXPECT_EQ(NamesOf(vpiMethods, defn),
            (std::vector<std::string>{"run", "size"}));
  vpiHandle run = Named(vpiMethods, defn, "run");
  EXPECT_EQ(vpi_get(vpiType, run), vpiTask);
  EXPECT_EQ(vpi_get(vpiMethod, run), 1);
  EXPECT_EQ(vpi_get(vpiVisibility, run), vpiProtectedVis);
  // §8.6 (#5052): a method's lifetime is automatic.
  EXPECT_EQ(vpi_get(vpiAutomatic, run), 1);
  EXPECT_EQ(vpi_get(vpiType, Named(vpiMethods, defn, "size")), vpiFunction);
}

// §37.41 detail 5 (#5046): a method is full-named through its class defn...
TEST_F(ClassDefinitionsOfARun, AMethodIsFullNamedThroughItsClass) {
  Run(kPacket);
  vpiHandle run = Named(vpiMethods, DefnIn(By("top"), "Packet"), "run");
  EXPECT_STREQ(vpi_get_str(vpiFullName, run), "top.Packet::run");
}

// ...and (#5047) reports whether it is virtual, pure virtual among them.
TEST_F(ClassDefinitionsOfARun, AVirtualMethodReportsVpiVirtual) {
  Run("module top; virtual class Shape;\n"
      "  virtual function int area(); return 0; endfunction\n"
      "  pure virtual function int sides();\n"
      "  function int id(); return 1; endfunction endclass endmodule\n");
  vpiHandle defn = DefnIn(By("top"), "Shape");
  EXPECT_EQ(vpi_get(vpiVirtual, Named(vpiMethods, defn, "area")), 1);
  EXPECT_EQ(vpi_get(vpiVirtual, Named(vpiMethods, defn, "sides")), 1);
  EXPECT_EQ(vpi_get(vpiVirtual, Named(vpiMethods, defn, "id")), 0);
}

// §37.31 detail 2: a named event array a class defn hands back is one of the
// value-bearing objects the value-access restriction is about.
TEST(ClassDefnValueAccess, ANamedEventArrayIsValueBearing) {
  EXPECT_TRUE(VpiIsClassMemberValueType(vpiNamedEventArray));
}
}  // namespace
}  // namespace delta
