#include <gtest/gtest.h>

#include <deque>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_vpi_run.h"
#include "parser/ast_class.h"
#include "simulator/class_object.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_class_objects.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_pool_keeper.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.32 class typespec: a class typespec is either a lexical construct or a
// class specialization, with name, class type, declared lifetime, and a set of
// relations. These tests observe the production helpers in class_object.cpp and
// the shared vpiAutomatic lifetime model from §37.3.7.

// C1 + C2: §37.32 rules that a class typespec represents either a lexical
// construct or a class specialization, and that the member-collection relations
// are unsupported on one representing only a lexical construct. The two forms
// are modeled distinctly here, in that VpiClassTypespecSupportsMembers is what
// tells them apart: this fails when either form answers the other's way.
TEST(ClassTypespec, LexicalTypespecDoesNotSupportMembers) {
  ClassTypespecInfo lexical;
  lexical.kind = ClassTypespecKind::kLexical;
  ClassTypespecInfo spec;
  spec.kind = ClassTypespecKind::kSpecialization;

  EXPECT_FALSE(VpiClassTypespecSupportsMembers(lexical));
  EXPECT_TRUE(VpiClassTypespecSupportsMembers(spec));
}

// C4: a specialization must carry a non-empty name.
TEST(ClassTypespec, SpecializationNameMustBeNonEmpty) {
  ClassTypespecInfo named;
  named.kind = ClassTypespecKind::kSpecialization;
  named.name = "Stack#(int)";
  ClassTypespecInfo unnamed;
  unnamed.kind = ClassTypespecKind::kSpecialization;
  unnamed.name = "";

  EXPECT_TRUE(VpiClassTypespecNameValid(named));
  EXPECT_FALSE(VpiClassTypespecNameValid(unnamed));
}

// C1 + C4 edge: the valid-name requirement applies only to specializations, so
// a purely lexical typespec with no name is still well formed.
TEST(ClassTypespec, LexicalTypespecNeedsNoName) {
  ClassTypespecInfo lexical;
  lexical.kind = ClassTypespecKind::kLexical;
  lexical.name = "";

  EXPECT_TRUE(VpiClassTypespecNameValid(lexical));
}

// C5: iterating methods returns both static and automatic methods but excludes
// built-in methods that have no explicit declaration.
TEST(ClassTypespec, MethodsExcludeUndeclaredBuiltins) {
  ClassTypespecInfo spec;
  spec.kind = ClassTypespecKind::kSpecialization;
  spec.methods.push_back(
      {"push", /*is_static=*/false, /*has_explicit_decl=*/true});
  spec.methods.push_back(
      {"create", /*is_static=*/true, /*has_explicit_decl=*/true});
  spec.methods.push_back(
      {"randomize", /*is_static=*/false, /*has_explicit_decl=*/false});

  std::vector<ClassTypespecMethod> visible = VpiClassTypespecMethods(spec);
  ASSERT_EQ(visible.size(), 2u);
  EXPECT_EQ(visible[0].name, "push");
  EXPECT_EQ(visible[1].name, "create");
}

// C2 + C5 edge: the member-collection relations are unsupported on a lexical
// typespec, so iterating its methods yields nothing even when entries are
// present.
TEST(ClassTypespec, LexicalTypespecYieldsNoMethods) {
  ClassTypespecInfo lexical;
  lexical.kind = ClassTypespecKind::kLexical;
  lexical.methods.push_back(
      {"push", /*is_static=*/false, /*has_explicit_decl=*/true});

  EXPECT_TRUE(VpiClassTypespecMethods(lexical).empty());
}

// C9: vpiExtends returns the base typespec, and the base typespec of a
// specialization is itself a specialization.
TEST(ClassTypespec, ExtendsReturnsSpecializationBase) {
  ClassTypespecInfo base;
  base.kind = ClassTypespecKind::kSpecialization;
  base.name = "Base#(int)";
  ClassTypespecInfo derived;
  derived.kind = ClassTypespecKind::kSpecialization;
  derived.name = "Derived#(int)";
  derived.extends = &base;

  EXPECT_EQ(VpiExtendsOf(derived), &base);
  EXPECT_TRUE(VpiClassTypespecBaseIsSpecialization(derived));

  // A specialization whose base is a lexical typespec violates the invariant.
  ClassTypespecInfo lexical_base;
  lexical_base.kind = ClassTypespecKind::kLexical;
  ClassTypespecInfo bad;
  bad.kind = ClassTypespecKind::kSpecialization;
  bad.extends = &lexical_base;
  EXPECT_FALSE(VpiClassTypespecBaseIsSpecialization(bad));
}

// C9 edge: a typespec that derives from nothing reports a null base and
// vacuously satisfies the base-is-a-specialization invariant.
TEST(ClassTypespec, TypespecWithoutBaseHasNullExtends) {
  ClassTypespecInfo root;
  root.kind = ClassTypespecKind::kSpecialization;
  root.name = "Root#(int)";

  EXPECT_EQ(VpiExtendsOf(root), nullptr);
  EXPECT_TRUE(VpiClassTypespecBaseIsSpecialization(root));
}

// C12: vpiLocalParam is true for parameters declared in the class body and
// false for parameter-port-list parameters.
TEST(ClassTypespec, LocalParamReflectsBodyDeclaration) {
  ClassTypespecParam port_param;
  port_param.name = "WIDTH";
  port_param.is_local_param = false;
  ClassTypespecParam body_param;
  body_param.name = "DEPTH";
  body_param.is_local_param = true;

  EXPECT_FALSE(VpiClassTypespecParamIsLocal(port_param));
  EXPECT_TRUE(VpiClassTypespecParamIsLocal(body_param));
}

// C13: vpiClassDefn returns NULL for built-in classes and the class otherwise.
TEST(ClassTypespec, ClassDefnIsNullForBuiltins) {
  ClassTypeInfo user_class;
  user_class.name = "MyClass";
  user_class.is_builtin = false;
  ClassTypeInfo builtin;
  builtin.name = "process";
  builtin.is_builtin = true;

  EXPECT_EQ(VpiClassDefnOf(user_class), &user_class);
  EXPECT_EQ(VpiClassDefnOf(builtin), nullptr);
}

// C14 weave: the class typespec's declared lifetime is the §37.3.7 vpiAutomatic
// property; the typespec carries the same Boolean field, and a VpiObject built
// from it reports the lifetime through vpi_get(vpiAutomatic).
TEST(ClassTypespec, DeclaredLifetimeReusesAutomaticModel) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  ClassTypespecInfo automatic_spec;
  automatic_spec.kind = ClassTypespecKind::kSpecialization;
  automatic_spec.automatic = true;

  VpiObject obj;
  obj.type = vpiClassTypespec;
  obj.automatic = automatic_spec.automatic;

  EXPECT_EQ(vpi_get(vpiAutomatic, VpiHandleOf(&obj)), 1);
}

// C3: vpiRhs of a parameter assignment is the explicit argument when supplied,
// and otherwise the declared default.
TEST(ClassTypespec, ParamRhsPrefersExplicitArgument) {
  ClassTypespecParamAssign explicit_arg;
  explicit_arg.name = "WIDTH";
  explicit_arg.has_explicit_arg = true;
  explicit_arg.explicit_rhs = "8";
  explicit_arg.default_rhs = "16";

  ClassTypespecParamAssign defaulted;
  defaulted.name = "WIDTH";
  defaulted.has_explicit_arg = false;
  defaulted.default_rhs = "16";

  EXPECT_EQ(VpiClassTypespecParamRhs(explicit_arg), "8");
  EXPECT_EQ(VpiClassTypespecParamRhs(defaulted), "16");
}

// C6: value access through a class typespec is disallowed for a non-static
// member but allowed for static members or when not reached via the typespec.
TEST(ClassTypespec, ValueAccessDisallowedForNonStaticTypespecMember) {
  EXPECT_FALSE(VpiClassTypespecValueAccessAllowed(
      /*obtained_from_class_typespec=*/true, /*is_static=*/false));
  EXPECT_TRUE(VpiClassTypespecValueAccessAllowed(
      /*obtained_from_class_typespec=*/true, /*is_static=*/true));
  EXPECT_TRUE(VpiClassTypespecValueAccessAllowed(
      /*obtained_from_class_typespec=*/false, /*is_static=*/false));
}

// C7 + C8: iterating constraints excludes inline constraints and keeps
// declaration order, with external constraints ordered by their prototype.
TEST(ClassTypespec, ConstraintsExcludeInlineAndKeepDeclarationOrder) {
  ClassTypespecInfo spec;
  spec.kind = ClassTypespecKind::kSpecialization;
  spec.constraints.push_back({"c_first", /*is_inline=*/false,
                              /*is_extern=*/false, /*decl_order=*/0,
                              /*prototype_order=*/0});
  spec.constraints.push_back({"c_inline", /*is_inline=*/true,
                              /*is_extern=*/false, /*decl_order=*/1,
                              /*prototype_order=*/0});
  spec.constraints.push_back({"c_extern", /*is_inline=*/false,
                              /*is_extern=*/true, /*decl_order=*/3,
                              /*prototype_order=*/1});
  spec.constraints.push_back({"c_last", /*is_inline=*/false,
                              /*is_extern=*/false, /*decl_order=*/2,
                              /*prototype_order=*/0});

  std::vector<ClassTypespecConstraint> visible =
      VpiClassTypespecConstraints(spec);
  ASSERT_EQ(visible.size(), 3u);
  EXPECT_EQ(visible[0].name, "c_first");
  EXPECT_EQ(visible[1].name, "c_extern");
  EXPECT_EQ(visible[2].name, "c_last");
}

// C10: a class definition reports the specializations that directly name it.
TEST(ClassTypespec, ClassDefnReportsDirectSpecializations) {
  ClassTypespecInfo spec_a;
  spec_a.name = "Stack#(int)";
  ClassTypespecInfo spec_b;
  spec_b.name = "Stack#(bit)";

  ClassTypeInfo cls;
  cls.name = "Stack";
  cls.direct_specializations = {&spec_a, &spec_b};

  std::vector<const ClassTypespecInfo*> specs =
      VpiClassDefnSpecializations(cls);
  ASSERT_EQ(specs.size(), 2u);
  EXPECT_EQ(specs[0], &spec_a);
  EXPECT_EQ(specs[1], &spec_b);
}

// C11: a virtual interface array expands to one variable per element when
// counted expanded, but collapses to a single variable when counted by array.
TEST(ClassTypespec, VirtualInterfaceArrayExpandsPerElement) {
  ClassTypespecInfo spec;
  spec.kind = ClassTypespecKind::kSpecialization;
  spec.vif_vars.push_back({"vif_scalar", /*array_size=*/0});
  spec.vif_vars.push_back({"vif_array", /*array_size=*/3});

  EXPECT_EQ(VpiClassTypespecVirtualInterfaceVarCount(spec), 4);
  EXPECT_EQ(VpiClassTypespecArrayVarCount(spec), 2);
}

// §37.32 details 1 and 3 (printed page 1043 of IEEE 1800-2023): a class
// typespec whose parameter values are all resolved represents a class
// specialization, and for such a typespec the vpiRhs of each param assignment
// may be any object carrying the value the parameter has, where a typespec
// representing only a lexical construct answers the explicit parameter
// expression or, failing that, the expression the parameter was declared with.
// The typespec built from a class type the run holds is the resolved one:
// §8.25 makes the specialization the type and the run keeps its parameters'
// values on it. Two parameters discriminate: the record carried the written
// expression's text alone and no value at all, and the type's own storage
// gives 4 and 8.
TEST(ClassTypespec, SpecializationTypespecCarriesItsResolvedParameterValues) {
  Arena arena;
  ClassDecl decl;
  decl.name = "vector";
  decl.params = {{"size", nullptr}, {"depth", nullptr}};
  decl.localparam_port_names.insert("depth");
  ClassTypeInfo spec;
  spec.name = "vector#(4,8)";
  spec.decl = &decl;
  spec.static_properties["size"] = MakeLogic4VecVal(arena, 32, 4);
  spec.static_properties["depth"] = MakeLogic4VecVal(arena, 32, 8);

  ClassTypespecInfo ts = VpiClassTypespecOf(&spec);

  EXPECT_EQ(ts.kind, ClassTypespecKind::kSpecialization);
  EXPECT_EQ(ts.name, "vector#(4,8)");
  EXPECT_EQ(ts.class_defn, &spec);
  ASSERT_EQ(ts.params.size(), 2u);
  EXPECT_EQ(ts.params[0].name, "size");
  EXPECT_FALSE(ts.params[0].is_local_param);
  EXPECT_EQ(ts.params[1].name, "depth");
  EXPECT_TRUE(ts.params[1].is_local_param);
  ASSERT_EQ(ts.param_assigns.size(), 2u);
  EXPECT_EQ(ts.param_assigns[0].name, "size");
  EXPECT_TRUE(ts.param_assigns[0].has_bound_value);
  EXPECT_EQ(ts.param_assigns[0].bound_value.ToUint64(), 4u);
  EXPECT_EQ(ts.param_assigns[1].name, "depth");
  EXPECT_TRUE(ts.param_assigns[1].has_bound_value);
  EXPECT_EQ(ts.param_assigns[1].bound_value.ToUint64(), 8u);
}

// §37.32 against designs read and run whole.
class ClassTypespecsOfARun : public VpiDesignRun {
 protected:
  // The integer value of `obj`, -1 where nothing is written.
  static int IntValueOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = -1;
    if (obj != nullptr) vpi_get_value(obj, &value);
    return value.value.integer;
  }

  // The class specialization typespec `defn` reaches through
  // vpiClassTypespec whose parameter `name` holds `value`, null for none.
  static vpiHandle SpecializationWith(vpiHandle defn, std::string_view name,
                                      int value) {
    for (vpiHandle typespec : ObjectsOf(vpiClassTypespec, defn)) {
      if (IntValueOf(Named(vpiParameter, typespec, name)) == value) {
        return typespec;
      }
    }
    return nullptr;
  }

  // The value each param assign `typespec` reaches assigns, by the name of
  // the parameter it assigns, in the order reached; -1 for none.
  static std::vector<std::pair<std::string, int>> AssignedValues(
      vpiHandle typespec) {
    std::vector<std::pair<std::string, int>> assigned;
    for (vpiHandle assign : ObjectsOf(vpiParamAssign, typespec)) {
      vpiHandle lhs = vpi_handle(vpiLhs, assign);
      assigned.emplace_back(lhs == nullptr ? "" : vpi_get_str(vpiName, lhs),
                            IntValueOf(vpi_handle(vpiRhs, assign)));
    }
    return assigned;
  }

  // What the param assign of the parameter `param` reaches through vpiRhs on
  // the typespec the extends clause of the class `derived`, which `scope`
  // declares, writes; null for none.
  static vpiHandle ExtendsRhs(const char* scope, const char* derived,
                              std::string_view param) {
    vpiHandle typespec = vpi_handle(
        vpiClassTypespec,
        vpi_handle(vpiExtends, Named(vpiClassDefn, By(scope), derived)));
    for (vpiHandle assign : ObjectsOf(vpiParamAssign, typespec)) {
      vpiHandle lhs = vpi_handle(vpiLhs, assign);
      if (lhs != nullptr && vpi_get_str(vpiName, lhs) == param) {
        return vpi_handle(vpiRhs, assign);
      }
    }
    return nullptr;
  }
};

constexpr const char* kSpecializations =
    "module top;\n"
    "  class B #(int W = 4, int V = 2);\n"
    "    rand int x;\n"
    "    event e;\n"
    "    constraint c { x > 0; }\n"
    "    task t; endtask\n"
    "  endclass\n"
    "  class D extends B #(8); endclass\n"
    "  class E extends B #(.V(5)); endclass\n"
    "  D d = new;\n"
    "  E en = new;\n"
    "  B #(3) b3 = new;\n"
    "  mailbox m = new;\n"
    "  semaphore s = new;\n"
    "endmodule\n";

// §37.32 details 1 and 10: a class defn reaches through vpiClassTypespec the
// class specializations of its class, each reaching the defn and reporting a
// user-defined class type (#7126, #7127).
TEST_F(ClassTypespecsOfARun, ADefnReachesItsSpecializations) {
  Run(kSpecializations);
  vpiHandle b = Named(vpiClassDefn, By("top"), "B");
  ASSERT_NE(b, nullptr);
  vpiHandle three = SpecializationWith(b, "W", 3);
  vpiHandle eight = SpecializationWith(b, "W", 8);
  ASSERT_NE(three, nullptr);
  ASSERT_NE(eight, nullptr);
  EXPECT_NE(three, eight);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClassDefn, three)), VpiObjectOf(b));
  EXPECT_EQ(vpi_get(vpiClassType, three), vpiUserDefinedClass);
  EXPECT_NE(vpi_get_str(vpiName, three), nullptr);
}

// §37.32 details 3, 5, 8 and 12: a specialization's typespec reaches the
// variables, methods, constraints and named events of its class, the methods
// alone being its internal scopes, and its parameters with the values the
// specialization gives them, each assigned by a param assign (#7125, #7128).
TEST_F(ClassTypespecsOfARun, ASpecializationReachesItsMembers) {
  Run(kSpecializations);
  vpiHandle three =
      SpecializationWith(Named(vpiClassDefn, By("top"), "B"), "W", 3);
  ASSERT_NE(three, nullptr);
  EXPECT_EQ(NamesOf(vpiVariables, three), (std::vector<std::string>{"x"}));
  EXPECT_EQ(NamesOf(vpiMethods, three), (std::vector<std::string>{"t"}));
  EXPECT_EQ(NamesOf(vpiConstraint, three), (std::vector<std::string>{"c"}));
  EXPECT_EQ(NamesOf(vpiNamedEvent, three), (std::vector<std::string>{"e"}));
  EXPECT_EQ(NamesOf(vpiInternalScope, three), (std::vector<std::string>{"t"}));
  EXPECT_EQ(IntValueOf(Named(vpiParameter, three, "V")), 2);
  EXPECT_EQ(AssignedValues(three),
            (std::vector<std::pair<std::string, int>>{{"W", 3}, {"V", 2}}));
}

// §37.32 details 1 and 9 with §37.33: a class obj's typespec is the class
// specialization it was created as, which extends the specialization of its
// base, itself extending none; a lexical typespec has no members (detail 2)
// (#7125).
TEST_F(ClassTypespecsOfARun, AClassObjsTypespecExtendsItsBasesSpecialization) {
  Run(kSpecializations);
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.d"));
  ASSERT_NE(obj, nullptr);
  vpiHandle typespec = vpi_handle(vpiClassTypespec, obj);
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClassDefn, typespec)),
            VpiObjectOf(Named(vpiClassDefn, By("top"), "D")));
  vpiHandle base = vpi_handle(vpiExtends, typespec);
  ASSERT_NE(base, nullptr);
  EXPECT_EQ(IntValueOf(Named(vpiParameter, base, "W")), 8);
  EXPECT_EQ(vpi_handle(vpiExtends, base), nullptr);
  vpiHandle lexical =
      vpi_handle(vpiClassTypespec,
                 vpi_handle(vpiExtends, Named(vpiClassDefn, By("top"), "D")));
  ASSERT_NE(lexical, nullptr);
  EXPECT_TRUE(NamesOf(vpiVariables, lexical).empty());
}

// §37.32 detail 3: the typespec an extends clause writes is a lexical
// construct, whose param assigns reach the expression the clause gives each
// parameter, by place or by name, and else the parameter's default (#7128).
TEST_F(ClassTypespecsOfARun, AnExtendsClausesTypespecAssignsWhatItWrites) {
  Run(kSpecializations);
  const auto kWritten = [](const char* derived) {
    return AssignedValues(vpi_handle(
        vpiClassTypespec,
        vpi_handle(vpiExtends, Named(vpiClassDefn, By("top"), derived))));
  };
  EXPECT_EQ(kWritten("D"),
            (std::vector<std::pair<std::string, int>>{{"W", 8}, {"V", 2}}));
  EXPECT_EQ(kWritten("E"),
            (std::vector<std::pair<std::string, int>>{{"W", 4}, {"V", 5}}));
}

// §37.32 detail 1: the type of a variable no class defn contains is a class
// specialization, so a module's class var reaches the typespec of the one it
// was declared as, with its class's members (#7372).
TEST_F(ClassTypespecsOfARun, AModulesClassVarIsOfItsSpecialization) {
  Run(kSpecializations);
  vpiHandle typespec = vpi_handle(vpiClassTypespec, By("top.b3"));
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(IntValueOf(Named(vpiParameter, typespec, "W")), 3);
  EXPECT_EQ(NamesOf(vpiVariables, typespec), (std::vector<std::string>{"x"}));
}

// §37.32 detail 3: a type an extends clause gives a type parameter, or the
// default type one was declared with, is assigned as a typespec of that type
// (#7371).
TEST_F(ClassTypespecsOfARun, AnExtendsClausesTypeIsAssignedItsTypespec) {
  Run("module top;\n"
      "  class B2 #(type T = int, int N = 1); endclass\n"
      "  class F extends B2 #(byte); endclass\n"
      "  class G extends B2; endclass\n"
      "endmodule\n");
  const auto kAssigned = [](const char* derived) {
    std::vector<int> kinds;
    vpiHandle typespec = vpi_handle(
        vpiClassTypespec,
        vpi_handle(vpiExtends, Named(vpiClassDefn, By("top"), derived)));
    for (vpiHandle assign : ObjectsOf(vpiParamAssign, typespec)) {
      vpiHandle rhs = vpi_handle(vpiRhs, assign);
      kinds.push_back(rhs == nullptr ? 0 : vpi_get(vpiType, rhs));
    }
    return kinds;
  };
  EXPECT_EQ(kAssigned("F"), (std::vector<int>{vpiByteTypespec, vpiConstant}));
  EXPECT_EQ(kAssigned("G"), (std::vector<int>{vpiIntTypespec, vpiConstant}));
}

// §37.32 detail 3: a type written as a name, given a type parameter by an
// extends clause or declared as its default, is assigned the typespec the
// name finds: a typedef's own, or a class typespec reaching the class's defn
// (#7374).
TEST_F(ClassTypespecsOfARun, AnExtendsClausesNamedTypeIsAssignedItsTypespec) {
  Run("module top;\n"
      "  typedef bit [3:0] nib_t;\n"
      "  class C; endclass\n"
      "  class B3 #(type T = nib_t, type U = int); endclass\n"
      "  class H extends B3 #(.U(C)); endclass\n"
      "  class J extends B3 #(nib_t, nib_t); endclass\n"
      "endmodule\n");
  vpiHandle nib = Named(vpiTypedef, By("top"), "nib_t");
  ASSERT_NE(nib, nullptr);
  EXPECT_EQ(VpiObjectOf(ExtendsRhs("top", "H", "T")), VpiObjectOf(nib));
  EXPECT_EQ(VpiObjectOf(ExtendsRhs("top", "J", "T")), VpiObjectOf(nib));
  EXPECT_EQ(VpiObjectOf(ExtendsRhs("top", "J", "U")), VpiObjectOf(nib));
  vpiHandle c = ExtendsRhs("top", "H", "U");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(vpi_get(vpiType, c), vpiClassTypespec);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClassDefn, c)),
            VpiObjectOf(Named(vpiClassDefn, By("top"), "C")));
}

// §37.32 detail 3: a class a package declares finds a type its extends clause
// gives as a name among the package's typedefs (#7374).
TEST_F(ClassTypespecsOfARun, APackagesExtendsClauseFindsThePackagesTypedef) {
  Run("package pk;\n"
      "  typedef byte b_t;\n"
      "  class PB #(type T = int); endclass\n"
      "  class PD extends PB #(b_t); endclass\n"
      "endpackage\n"
      "module top;\n"
      "  pk::PD d = new;\n"
      "endmodule\n");
  vpiHandle b = Named(vpiTypedef, By("pk"), "b_t");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(VpiObjectOf(ExtendsRhs("pk", "PD", "T")), VpiObjectOf(b));
}

// §37.32 detail 3 with §27.4: a class a generate block declares finds a type
// its extends clause gives as a name among the typedefs of the blocks
// enclosing it, the innermost first, before the module's (#7381).
TEST_F(ClassTypespecsOfARun,
       AGenerateBlocksExtendsClauseFindsTheBlocksTypedef) {
  Run("module top;\n"
      "  typedef byte nib_t;\n"
      "  typedef int m_t;\n"
      "  class B #(type T = int, type U = int); endclass\n"
      "  if (1) begin : g\n"
      "    typedef bit [3:0] nib_t;\n"
      "    if (1) begin : h\n"
      "      class D extends B #(nib_t, m_t); endclass\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  vpiHandle nib = Named(vpiTypedef, By("top.g"), "nib_t");
  vpiHandle m = Named(vpiTypedef, By("top"), "m_t");
  ASSERT_NE(nib, nullptr);
  ASSERT_NE(m, nullptr);
  EXPECT_EQ(VpiObjectOf(ExtendsRhs("top.g.h", "D", "T")), VpiObjectOf(nib));
  EXPECT_EQ(VpiObjectOf(ExtendsRhs("top.g.h", "D", "U")), VpiObjectOf(m));
}

// §37.32: the typespec of a mailbox's and a semaphore's class obj reports the
// built-in class it stands for (#7126).
TEST_F(ClassTypespecsOfARun, ABuiltInClassReportsItsClassType) {
  Run(kSpecializations);
  const auto kTypeOf = [](const char* var) {
    return vpi_get(vpiClassType, vpi_handle(vpiClassTypespec,
                                            vpi_handle(vpiClassObj, By(var))));
  };
  EXPECT_EQ(kTypeOf("top.m"), vpiMailboxClass);
  EXPECT_EQ(kTypeOf("top.s"), vpiSemaphoreClass);
}

// §37.32 with §38.6: vpiClassType is drawn on a class typespec alone, so a
// class defn, a class obj and a module, none of which carries it, answer
// vpiUndefined (#8189).
TEST_F(ClassTypespecsOfARun, AnObjectOtherThanAClassTypespecHasNoClassType) {
  Run(kSpecializations);
  vpiHandle b = Named(vpiClassDefn, By("top"), "B");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(vpi_get(vpiClassType, b), vpiUndefined);
  EXPECT_EQ(vpi_get(vpiClassType, vpi_handle(vpiClassObj, By("top.m"))),
            vpiUndefined);
  EXPECT_EQ(vpi_get(vpiClassType, By("top")), vpiUndefined);
}

// §37.32 detail 1 with §37.33: a class obj of a class no class defn stands
// for still holds a typespec of its class, reaching no defn.
TEST(ClassObjTypespec, AClassWithNoDefnHasATypespecOfItsOwn) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  ClassDecl decl;
  decl.name = "C";
  ClassTypeInfo type;
  type.name = "C";
  type.decl = &decl;
  ClassObject obj;
  obj.type = &type;
  std::vector<std::unique_ptr<VpiObject>> pool;
  std::deque<std::string> names;
  const VpiAttachBuild kBuild{[&pool] {
                                pool.push_back(std::make_unique<VpiObject>());
                                return pool.back().get();
                              },
                              VpiPoolKeeper(names), arena};
  const VpiClassCallSite kSite;
  const VpiClassObjDefn kOf{
      [](const ClassTypeInfo&) -> VpiObject* { return nullptr; },
      [&kSite](const VpiObject*) -> const VpiClassCallSite& { return kSite; }};
  VpiObject* made = VpiMakeClassObject(obj, kOf, {}, ctx, kBuild);
  ASSERT_FALSE(made->children.empty());
  const VpiObject* typespec = made->children.front();
  EXPECT_EQ(typespec->type, vpiClassTypespec);
  EXPECT_EQ(typespec->name, "C");
  EXPECT_TRUE(typespec->children.empty());
}

}  // namespace
}  // namespace delta
