#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(TypeParameterElab, LocalparamTypeElaboratesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam type T = byte;\n"
      "  T data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "data");
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(TypeParameterElab, MultipleTypeParamsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter type A = int;\n"
      "  parameter type B = shortint;\n"
      "  A x;\n"
      "  B y;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 2u);
  EXPECT_EQ(mod->variables[0].width, 32u);
  EXPECT_EQ(mod->variables[1].width, 16u);
}

TEST(TypeParameterElab, TypeParamLogicVectorWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter type T = logic [7:0];\n"
      "  T bus;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "bus");
  EXPECT_EQ(mod->variables[0].width, 8u);
}

// §6.20.3: a data type parameter can only be set to a data type. Giving a
// `parameter type` an ordinary value expression as its default must be an
// error.
TEST(TypeParameterElab, TypeParamSetToValueIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter type T = 5;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.20.3: a type parameter restricted with a leading basic data type keyword
// must be assigned a conforming type. An `enum`-restricted type parameter
// bound to a non-enum type does not conform and must be rejected.
TEST(TypeParameterElab, RestrictedEnumTypeParamMismatchIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter type enum E = int;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.20.3: when the assigned type does conform to the restriction keyword the
// declaration is legal. An `enum`-restricted type parameter bound to an enum
// typedef conforms and must elaborate without error.
TEST(TypeParameterElab, RestrictedEnumTypeParamConformsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum {A, B} my_enum_t;\n"
      "  parameter type enum E = my_enum_t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.20.3: the restriction keyword may also be `struct` (the same forward-type
// keyword set §6.18 uses). A `struct`-restricted type parameter bound to a
// non-struct type does not conform and must be rejected.
TEST(TypeParameterElab, RestrictedStructTypeParamMismatchIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter type struct S = int;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.20.3: a `struct`-restricted type parameter bound to a struct typedef
// conforms to the specified basic data type and must elaborate cleanly.
TEST(TypeParameterElab, RestrictedStructTypeParamConformsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } s_t;\n"
      "  parameter type struct S = s_t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.20.3: likewise a `union`-restricted type parameter bound to a non-union
// type does not conform to the specified basic data type and must be rejected.
TEST(TypeParameterElab, RestrictedUnionTypeParamMismatchIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter type union U = int;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.20.3: a `union`-restricted type parameter bound to a union typedef
// conforms to the specified basic data type and must elaborate cleanly (the
// positive counterpart of RestrictedUnionTypeParamMismatchIsError).
TEST(TypeParameterElab, RestrictedUnionTypeParamConformsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef union packed { logic [7:0] a; logic [7:0] b; } u_t;\n"
      "  parameter type union U = u_t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.20.3: the restriction keyword may also be `class`. A `class`-restricted
// type parameter assigned a built-in (non-class) type does not conform and must
// be rejected.
TEST(TypeParameterElab, RestrictedClassTypeParamMismatchIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter type class C = int;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.20.3: a `class`-restricted type parameter assigned an actual class type
// conforms and must elaborate cleanly (the positive counterpart of
// RestrictedClassTypeParamMismatchIsError).
TEST(TypeParameterElab, RestrictedClassTypeParamConformsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class my_cls;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  parameter type class C = my_cls;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.20.3: the restriction keyword may also be `interface class`. An
// `interface class`-restricted type parameter assigned a built-in (non-class)
// type does not conform and must be rejected.
TEST(TypeParameterElab, RestrictedInterfaceClassTypeParamMismatchIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter type interface class IC = int;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.20.3: a type parameter's default may itself be a user-defined type name
// (from §6.18's typedef), not just a built-in keyword. The type parameter must
// resolve through that typedef so a dependent variable gets the named type's
// width. Built from the §6.18 typedef dependency's real syntax and driven
// through parse+elaborate.
TEST(TypeParameterElab, NamedTypedefTypeParamDefaultResolvesWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  parameter type T = byte_t;\n"
      "  T x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "x");
  EXPECT_EQ(mod->variables[0].width, 8u);
}

// §6.20.3: a type parameter used as a class scope resolution prefix (here in a
// typedef declaration, an allowed context) shall resolve to a class. A type
// parameter bound to a non-class type does not, so it must be rejected.
TEST(TypeParameterElab, TypeParamScopePrefixNotAClassIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter type T = int;\n"
      "  typedef T::inner my_t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.20.3: a type parameter may resolve to a class type, but using it as the
// prefix of the class scope resolution operator is restricted to typedef
// declarations, the type operator, and type parameter assignments. Here the
// type parameter prefixes '::' inside an ordinary expression, which is not one
// of the permitted contexts, so elaboration must report an error.
TEST(TypeParameterElab, TypeParamScopePrefixInExpressionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  static int val = 7;\n"
      "endclass\n"
      "module m;\n"
      "  parameter type T = C;\n"
      "  int x;\n"
      "  initial x = T::val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.20.3: overriding a type parameter with a defparam statement is illegal.
// The child's T is a parameter-port type parameter, so the hierarchical
// defparam targeting it must be rejected.
TEST(TypeParameterElab, DefparamCannotOverrideTypeParam) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(parameter type T = int)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.T = 16;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.20.3: the scope-resolution restriction also covers a type parameter that
// is declared in the parameter port list (not just the module body) and that
// appears as a '::' prefix inside a continuous assignment. This exercises the
// port-list collection and continuous-assign paths of the elaborator check.
TEST(TypeParameterElab, PortTypeParamScopePrefixInContAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter type T = int) ();\n"
      "  wire w;\n"
      "  assign w = T::n;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.20.3: the restriction is specific to a type parameter prefix. A type
// parameter used as an ordinary data type, and a genuine class name used as a
// scope resolution prefix, are both legal and must elaborate cleanly.
TEST(TypeParameterElab, TypeParamAsTypeWithClassScopeOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  static int count = 5;\n"
             "endclass\n"
             "module m;\n"
             "  parameter type T = int;\n"
             "  T data;\n"
             "  int x;\n"
             "  initial x = C::count;\n"
             "endmodule\n"));
}

}  // namespace
