#include <gtest/gtest.h>

#include <vector>

#include "simulator/class_object.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.32 class typespec: a class typespec is either a lexical construct or a
// class specialization, with name, class type, declared lifetime, and a set of
// relations. These tests observe the production helpers in class_object.cpp and
// the shared vpiAutomatic lifetime model from §37.3.7.

// C1: the two typespec forms are modeled distinctly.
TEST(ClassTypespec, KindDistinguishesLexicalAndSpecialization) {
  ClassTypespecInfo lexical;
  lexical.kind = ClassTypespecKind::kLexical;
  ClassTypespecInfo spec;
  spec.kind = ClassTypespecKind::kSpecialization;

  EXPECT_NE(static_cast<int>(lexical.kind), static_cast<int>(spec.kind));
}

// C2: a lexical-only typespec does not support the member-collection relations;
// a specialization does.
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

  EXPECT_EQ(vpi_get(vpiAutomatic, &obj), 1);
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

}  // namespace
}  // namespace delta
