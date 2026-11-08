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

TEST_F(ClassDefinition, ClassMethodsIterationExcludesImplicitBuiltins) {
  VpiObject declared_func;
  declared_func.type = vpiFunction;
  VpiObject implicit_builtin;
  implicit_builtin.type = vpiFunction;
  implicit_builtin.implicit_builtin_method = true;
  VpiObject declared_task;
  declared_task.type = vpiTask;
  VpiObject member_var;
  member_var.type = vpiLogicVar;

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
    value.value.integer = 0x5eed;

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

TEST_F(ClassDefinition, ValueRestrictionAppliesOnlyToVariableAndEventMembers) {
  VpiObject class_defn;
  class_defn.type = vpiClassDefn;

  VpiObject member_constraint;
  member_constraint.type = vpiConstraint;
  member_constraint.parent = &class_defn;

  s_vpi_value value = {};
  value.format = vpiIntVal;

  vpi_get_value(VpiHandleOf(&member_constraint), &value);
  s_vpi_error_info get_info = {};
  EXPECT_EQ(vpi_chk_error(&get_info), 0);

  vpi_put_value(VpiHandleOf(&member_constraint), &value, nullptr, vpiNoDelay);
  s_vpi_error_info put_info = {};
  ASSERT_EQ(vpi_chk_error(&put_info), vpiError);
  EXPECT_STREQ(put_info.message,
               "vpi_put_value(): a value can be put only to a net, a "
               "variable, a variable select, a named event, a system "
               "function call, a sequential UDP or a scheduled event");
}

TEST_F(ClassDefinition, ConstraintIterationExcludesInlineConstraints) {
  VpiObject normal_a;
  normal_a.type = vpiConstraint;
  VpiObject inline_c;
  inline_c.type = vpiConstraint;
  inline_c.inline_constraint = true;
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

TEST_F(ClassDefinition, ParameterIterationReportsPortAndBodyWithLocalParam) {
  VpiObject port_param;
  port_param.type = vpiParameter;
  port_param.local_param = false;
  VpiObject not_a_param;
  not_a_param.type = vpiConstraint;
  VpiObject body_param;
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

  EXPECT_EQ(vpi_get(vpiLocalParam, VpiHandleOf(&port_param)), 0);
  EXPECT_EQ(vpi_get(vpiLocalParam, VpiHandleOf(&body_param)), 1);
}

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

class ClassDefinitionsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle DefnIn(vpiHandle scope, std::string_view name) {
    return Named(vpiClassDefn, scope, name);
  }
};

TEST_F(ClassDefinitionsOfARun, AModuleClassIsAClassDefnOfItsInstance) {
  Run("module top; class Packet; endclass endmodule\n");
  EXPECT_EQ(NamesOf(vpiClassDefn, By("top")),
            std::vector<std::string>{"Packet"});
  vpiHandle defn = By("top.Packet");
  ASSERT_NE(defn, nullptr);
  EXPECT_EQ(vpi_get(vpiType, defn), vpiClassDefn);
  EXPECT_STREQ(vpi_get_str(vpiFullName, defn), "top.Packet");
}

TEST_F(ClassDefinitionsOfARun, AVirtualClassReportsVpiVirtual) {
  Run("module top; virtual class Shape; endclass\n"
      "  class Square extends Shape; endclass endmodule\n");
  EXPECT_EQ(vpi_get(vpiVirtual, DefnIn(By("top"), "Shape")), 1);
  EXPECT_EQ(vpi_get(vpiVirtual, DefnIn(By("top"), "Square")), 0);
}

TEST_F(ClassDefinitionsOfARun, APackageClassIsAClassDefnOfThePackage) {
  Run("package pkg; class Item; endclass endpackage\n"
      "module top; endmodule\n");
  vpiHandle defn = DefnIn(By("pkg"), "Item");
  ASSERT_NE(defn, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, defn), "pkg::Item");
}

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

TEST_F(ClassDefinitionsOfARun, ABaseNamedThroughAPackageIsThePackagesClass) {
  Run("package p; class Base; endclass endpackage\n"
      "module top; class Base; endclass\n"
      "  class Derived extends p::Base; endclass endmodule\n");
  vpiHandle typespec = vpi_handle(
      vpiClassTypespec, vpi_handle(vpiExtends, DefnIn(By("top"), "Derived")));
  ASSERT_NE(typespec, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, typespec), "Base");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClassDefn, typespec)),
            VpiObjectOf(DefnIn(By("p"), "Base")));
  EXPECT_TRUE(NamesOf(vpiDerivedClasses, DefnIn(By("top"), "Base")).empty());
}

TEST_F(ClassDefinitionsOfARun, ABaseClassIteratesItsDerivedClasses) {
  Run("module top; class Base; endclass class A extends Base; endclass\n"
      "  class B extends Base; endclass class C; endclass endmodule\n");
  EXPECT_EQ(NamesOf(vpiDerivedClasses, DefnIn(By("top"), "Base")),
            (std::vector<std::string>{"A", "B"}));
}

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

TEST_F(ClassDefinitionsOfARun, AClassDefnIteratesItsProperties) {
  Run(kPacket);
  vpiHandle defn = DefnIn(By("top"), "Packet");
  EXPECT_EQ(NamesOf(vpiVariables, defn),
            (std::vector<std::string>{"Id", "len", "tag"}));
  EXPECT_EQ(vpi_get(vpiType, Named(vpiVariables, defn, "tag")), vpiByteVar);
}

TEST_F(ClassDefinitionsOfARun, AStaticPropertyIsNamedThroughItsClass) {
  Run(kPacket);
  vpiHandle id = By("top.Packet::Id");
  ASSERT_NE(id, nullptr);
  EXPECT_EQ(vpi_get(vpiType, id), vpiIntVar);
  EXPECT_STREQ(vpi_get_str(vpiFullName, id), "top.Packet::Id");
}

TEST_F(ClassDefinitionsOfARun, APropertyReportsItsVisibility) {
  Run(kPacket);
  vpiHandle defn = DefnIn(By("top"), "Packet");
  EXPECT_EQ(vpi_get(vpiVisibility, Named(vpiVariables, defn, "tag")),
            vpiLocalVis);
  EXPECT_EQ(vpi_get(vpiVisibility, Named(vpiVariables, defn, "len")),
            vpiPublicVis);
}

TEST_F(ClassDefinitionsOfARun, AClassDefnIteratesItsMethods) {
  Run(kPacket);
  vpiHandle defn = DefnIn(By("top"), "Packet");
  EXPECT_EQ(NamesOf(vpiMethods, defn),
            (std::vector<std::string>{"run", "size"}));
  vpiHandle run = Named(vpiMethods, defn, "run");
  EXPECT_EQ(vpi_get(vpiType, run), vpiTask);
  EXPECT_EQ(vpi_get(vpiMethod, run), 1);
  EXPECT_EQ(vpi_get(vpiVisibility, run), vpiProtectedVis);
  EXPECT_EQ(vpi_get(vpiAutomatic, run), 1);
  EXPECT_EQ(vpi_get(vpiType, Named(vpiMethods, defn, "size")), vpiFunction);
}

TEST_F(ClassDefinitionsOfARun, AMethodIsFullNamedThroughItsClass) {
  Run(kPacket);
  vpiHandle run = Named(vpiMethods, DefnIn(By("top"), "Packet"), "run");
  EXPECT_STREQ(vpi_get_str(vpiFullName, run), "top.Packet::run");
}

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

TEST_F(ClassDefinitionsOfARun, AClassDefnIteratesItsTypedefs) {
  Run("module top; class C; typedef int T; localparam type U = byte;\n"
      "  typedef logic [3:0] N; int x; endclass endmodule\n");
  vpiHandle defn = DefnIn(By("top"), "C");
  EXPECT_EQ(NamesOf(vpiTypedef, defn), (std::vector<std::string>{"N", "T"}));
  vpiHandle t = Named(vpiTypedef, defn, "T");
  ASSERT_NE(t, nullptr);
  EXPECT_EQ(vpi_get(vpiType, t), vpiIntTypespec);
  EXPECT_STREQ(vpi_get_str(vpiFullName, t), "top.C::T");
}

TEST_F(ClassDefinitionsOfARun, AClassDefnIteratesItsParameters) {
  Run("module top; class C #(int W = 4, type T = int, localparam int L = 2);\n"
      "  parameter int P = 1; localparam type U = T; int x; endclass\n"
      "  class D; parameter type V = byte; endclass endmodule\n");
  vpiHandle c = DefnIn(By("top"), "C");
  EXPECT_EQ(NamesOf(vpiParameter, c),
            (std::vector<std::string>{"L", "P", "T", "U", "W"}));
  const auto kTypeOf = [&](std::string_view name) {
    return vpi_get(vpiType, Named(vpiParameter, c, name));
  };
  const auto kLocalOf = [&](std::string_view name) {
    return vpi_get(vpiLocalParam, Named(vpiParameter, c, name));
  };
  EXPECT_EQ(kTypeOf("W"), vpiParameter);
  EXPECT_EQ(kTypeOf("T"), vpiTypeParameter);
  EXPECT_EQ(kTypeOf("P"), vpiParameter);
  EXPECT_EQ(kTypeOf("U"), vpiTypeParameter);
  EXPECT_EQ(kLocalOf("W"), 0);
  EXPECT_EQ(kLocalOf("T"), 0);
  EXPECT_EQ(kLocalOf("L"), 1);
  EXPECT_EQ(kLocalOf("P"), 1);
  EXPECT_EQ(kLocalOf("U"), 1);
  EXPECT_STREQ(vpi_get_str(vpiFullName, Named(vpiParameter, c, "W")),
               "top.C::W");
  vpiHandle v = Named(vpiParameter, DefnIn(By("top"), "D"), "V");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(vpi_get(vpiType, v), vpiTypeParameter);
  EXPECT_EQ(vpi_get(vpiLocalParam, v), 1);
}

TEST_F(ClassDefinitionsOfARun, AClassDefnIteratesItsNamedEventArrays) {
  Run("module top; class C; event e; event ea[2]; int ia[2]; endclass\n"
      "endmodule\n");
  vpiHandle defn = DefnIn(By("top"), "C");
  EXPECT_EQ(NamesOf(vpiNamedEventArray, defn), std::vector<std::string>{"ea"});
  EXPECT_EQ(NamesOf(vpiNamedEvent, defn), std::vector<std::string>{"e"});
  EXPECT_EQ(NamesOf(vpiVariables, defn), std::vector<std::string>{"ia"});
}

TEST_F(ClassDefinitionsOfARun, ANestedClassIsAnInternalScopeOfItsClass) {
  Run("class U; class UN; endclass endclass\n"
      "module top; class C; class N; int k; class M; endclass endclass\n"
      "  int x; endclass endmodule\n");
  vpiHandle c = DefnIn(By("top"), "C");
  EXPECT_EQ(NamesOf(vpiInternalScope, c), std::vector<std::string>{"N"});
  vpiHandle n = Named(vpiInternalScope, c, "N");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(vpi_get(vpiType, n), vpiClassDefn);
  EXPECT_STREQ(vpi_get_str(vpiFullName, n), "top.C::N");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, n)), VpiObjectOf(c));
  EXPECT_EQ(NamesOf(vpiVariables, n), std::vector<std::string>{"k"});
  vpiHandle m = Named(vpiInternalScope, n, "M");
  ASSERT_NE(m, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, m), "top.C::N::M");
  EXPECT_EQ(NamesOf(vpiClassDefn, nullptr), std::vector<std::string>{"U"});
}

TEST(ClassDefnValueAccess, ANamedEventArrayIsValueBearing) {
  EXPECT_TRUE(VpiIsClassMemberValueType(vpiNamedEventArray));
}

TEST_F(ClassDefinitionsOfARun, AnOutOfBlockMethodIsNoTaskOfItsScope) {
  Run("package pk; class P; extern task pout(); endclass\n"
      "  task P::pout(); endtask task pt; endtask endpackage\n"
      "module top; class C; extern task outside(); endclass\n"
      "  task C::outside(); endtask task own; endtask endmodule\n");
  EXPECT_EQ(NamesOf(vpiTaskFunc, By("top")), std::vector<std::string>{"own"});
  EXPECT_EQ(NamesOf(vpiMethods, DefnIn(By("top"), "C")),
            std::vector<std::string>{"outside"});
  EXPECT_EQ(NamesOf(vpiTaskFunc, By("pk")), std::vector<std::string>{"pt"});
}

TEST_F(ClassDefinitionsOfARun, AnOutOfBlockMethodIsNoTaskOfTheUnit) {
  Run("int g;\n"
      "class U; extern task uout(); endclass\n"
      "task U::uout(); endtask\n"
      "task ut; endtask\n"
      "module top; endmodule\n");
  vpiHandle it = vpi_iterate(vpiPackage, nullptr);
  ASSERT_NE(it, nullptr);
  vpiHandle unit = vpi_scan(it);
  vpi_release_handle(it);
  EXPECT_EQ(NamesOf(vpiTaskFunc, unit), std::vector<std::string>{"ut"});
}

TEST_F(ClassDefinitionsOfARun, APropertyReachesItsTypespec) {
  Run("module top;\n"
      "  class C;\n"
      "    typedef bit [3:0] nib_t;\n"
      "    int x;\n"
      "    logic [7:0] b;\n"
      "    nib_t n;\n"
      "    event e;\n"
      "  endclass\n"
      "endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(defn, nullptr);
  const auto kTypespecOf = [defn](const char* name) {
    vpiHandle property = Named(vpiVariables, defn, name);
    if (property == nullptr) property = Named(vpiNamedEvent, defn, name);
    return property == nullptr ? nullptr : vpi_handle(vpiTypespec, property);
  };
  vpiHandle of_x = kTypespecOf("x");
  ASSERT_NE(of_x, nullptr);
  EXPECT_EQ(vpi_get(vpiType, of_x), vpiIntTypespec);
  vpiHandle of_b = kTypespecOf("b");
  ASSERT_NE(of_b, nullptr);
  EXPECT_EQ(vpi_get(vpiType, of_b), vpiLogicTypespec);
  EXPECT_NE(vpi_iterate(vpiRange, of_b), nullptr);
  vpiHandle of_n = kTypespecOf("n");
  ASSERT_NE(of_n, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, of_n), "nib_t");
  vpiHandle of_e = kTypespecOf("e");
  ASSERT_NE(of_e, nullptr);
  EXPECT_EQ(vpi_get(vpiType, of_e), vpiEventTypespec);
}

TEST_F(ClassDefinitionsOfARun, AGenerateBlocksClassIsAClassDefnOfEachInstance) {
  Run("module top;\n"
      "  class B; endclass\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    class C; endclass\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiClassDefn, By("top")), std::vector<std::string>{"B"});
  vpiHandle g0 = By("top.g[0]");
  vpiHandle c0 = DefnIn(g0, "C");
  vpiHandle c1 = DefnIn(By("top.g[1]"), "C");
  ASSERT_NE(c0, nullptr);
  ASSERT_NE(c1, nullptr);
  EXPECT_NE(VpiObjectOf(c0), VpiObjectOf(c1));
  EXPECT_STREQ(vpi_get_str(vpiFullName, c0), "top.g[0].C");
  EXPECT_STREQ(vpi_get_str(vpiFullName, c1), "top.g[1].C");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, c0)), VpiObjectOf(g0));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, c0)), VpiObjectOf(By("top")));
  EXPECT_EQ(NamesOf(vpiInternalScope, g0), std::vector<std::string>{"C"});
}

TEST_F(ClassDefinitionsOfARun, AGenerateBlocksClassExtendsAClassAroundIt) {
  Run("module top;\n"
      "  class B; endclass\n"
      "  if (1) begin : g\n"
      "    class E; endclass\n"
      "    if (1) begin : h\n"
      "      class D extends B; endclass\n"
      "      class F extends E; endclass\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  const auto kBaseOf = [](vpiHandle derived) {
    return VpiObjectOf(vpi_handle(
        vpiClassDefn,
        vpi_handle(vpiClassTypespec, vpi_handle(vpiExtends, derived))));
  };
  vpiHandle h = By("top.g.h");
  ASSERT_NE(DefnIn(By("top"), "B"), nullptr);
  ASSERT_NE(DefnIn(By("top.g"), "E"), nullptr);
  EXPECT_EQ(kBaseOf(DefnIn(h, "D")), VpiObjectOf(DefnIn(By("top"), "B")));
  EXPECT_EQ(kBaseOf(DefnIn(h, "F")), VpiObjectOf(DefnIn(By("top.g"), "E")));
}

TEST_F(ClassDefinitionsOfARun, ALoopGenerateBlocksClassExtendsTheModulesClass) {
  Run("module top;\n"
      "  class B; endclass\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    class C extends B; endclass\n"
      "  end\n"
      "endmodule\n");
  vpiHandle b = DefnIn(By("top"), "B");
  ASSERT_NE(b, nullptr);
  vpiHandle extends = vpi_handle(vpiExtends, DefnIn(By("top.g[1]"), "C"));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClassDefn,
                                   vpi_handle(vpiClassTypespec, extends))),
            VpiObjectOf(b));
}

TEST_F(ClassDefinitionsOfARun, APropertyOfAPackagesTypedefHasItsKind) {
  Run("package a; typedef int t; endpackage\n"
      "package p;\n"
      "  typedef real r;\n"
      "  class C; r own; a::t other; endclass\n"
      "endpackage\n"
      "module top; endmodule\n");
  vpiHandle defn = DefnIn(By("p"), "C");
  ASSERT_NE(defn, nullptr);
  EXPECT_EQ(vpi_get(vpiType, Named(vpiVariables, defn, "own")), vpiRealVar);
  EXPECT_EQ(vpi_get(vpiType, Named(vpiVariables, defn, "other")), vpiIntVar);
}
}  // namespace
}  // namespace delta
