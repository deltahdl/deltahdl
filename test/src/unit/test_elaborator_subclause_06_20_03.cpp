#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type parameter 'T' can only be set to a data type",
                            2, "6.20.3"));
}

// §6.20.3: a type parameter restricted with a leading basic data type keyword
// must be assigned a conforming type. An `enum`-restricted type parameter
// bound to a non-enum type does not conform and must be rejected. The report
// names §6.20.3, the subclause that states the restriction keyword, and so do
// the struct, union, class and interface class cases below.
TEST(TypeParameterElab, RestrictedEnumTypeParamMismatchIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter type enum E = int;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type parameter 'E' is assigned a type that does not conform to the "
      "required enum kind",
      2, "6.20.3"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type parameter 'S' is assigned a type that does not conform to the "
      "required struct kind",
      2, "6.20.3"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type parameter 'U' is assigned a type that does not conform to the "
      "required union kind",
      2, "6.20.3"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type parameter 'C' is restricted to a class type",
                            2, "6.20.3"));
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

// §6.20.3: a name that no class declaration defines conforms to a `class`
// restriction no more than a built-in type does, so the assignment is an error.
// The name has to answer two questions at once, and §19.3's covergroup is what
// answers both. Parser::ParseDataType in src/parser/parser_types.cpp reads an
// identifier as a type only when an earlier declaration registered it, and
// Parser::ParseCovergroupDecl in src/parser/parser_verify.cpp registers a
// covergroup name; a name declared nowhere at all reads as an expression
// instead, which is TypeParamSetToValueIsError's rule rather than this one. And
// the name has to reach no data type either, so that CheckTypeParamIsClass in
// src/elaborator/elaborator_items.cpp gets past its first branch, which answers
// for a resolved concrete type. A typedef of a built-in -- `typedef int
// my_type;` -- is registered but resolves, and so takes that first branch and
// reports a type that is not a class, which is
// RestrictedClassTypeParamMismatchIsError's rule. A covergroup name resolves to
// no data type and no ClassDecl, so it is the case this test is for.
TEST(TypeParameterElab, ClassTypeParamAssignedUndeclaredNameIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  covergroup cg;\n"
      "  endgroup\n"
      "  parameter type class C = cg;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type parameter 'C' is restricted to a class type "
                            "but is assigned 'cg', which no class declaration "
                            "defines",
                            4, "6.20.3"));
}

// §6.20.3: the built-in classes §15.x predefines conform to a `class`
// restriction, and `mailbox` is one of them. No ClassDecl declares it, so the
// elaborator answers for it from its set of known class names instead. A check
// that demanded a ClassDecl of every assigned name would reject every built-in
// class, and this is the case that says so.
TEST(TypeParameterElab, ClassTypeParamAssignedABuiltInClassIsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter type class C = mailbox;\n"
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
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "type parameter 'IC' is restricted to an interface class "
                    "type but is assigned a type that is not a class",
                    2, "6.20.3"));
}

// §6.20.3: `class` and `interface class` are two of the five basic data types
// the clause lists, and §8.26 makes them different kinds of declaration, so an
// ordinary class does not conform to an `interface class` restriction. The
// assigned name reaches a ClassDecl here, which is what separates this from
// ClassTypeParamAssignedUndeclaredNameIsError above; that declaration's
// is_interface is false, so the report names the kind the name does have.
TEST(TypeParameterElab, InterfaceClassTypeParamAssignedOrdinaryClassIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class my_cls;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  parameter type interface class IC = my_cls;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type parameter 'IC' is restricted to an interface "
                            "class type but is assigned 'my_cls', which is an "
                            "ordinary class",
                            5, "6.20.3"));
}

// §6.20.3: an `interface class`-restricted type parameter assigned an interface
// class conforms to the specified basic data type and must elaborate cleanly.
// A check that rejected every name, rather than reading
// ClassDecl::is_interface, would reject this source while still passing
// InterfaceClassTypeParamAssignedOrdinaryClassIsError above.
TEST(TypeParameterElab, InterfaceClassTypeParamAssignedInterfaceClassIsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface class ic;\n"
      "  pure virtual function void f();\n"
      "endclass\n"
      "module m;\n"
      "  parameter type interface class IC = ic;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type parameter 'T' used as a class scope "
                            "resolution prefix does not resolve to a class",
                            3, "6.20.3"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type parameter 'T' may prefix the class scope "
                            "resolution operator only within",
                            7, "6.20.3"));
}

// §6.20.3: overriding a type parameter with a defparam statement is illegal.
// The child's T is a parameter-port type parameter, so the hierarchical
// defparam targeting it must be rejected. §23.10.1 states the rule for the
// defparam statement, so the report names that subclause.
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "defparam cannot override a type parameter", 5,
                            "23.10.1"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type parameter 'T' may prefix the class scope "
                            "resolution operator only within",
                            3, "6.20.3"));
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

// §6.20.3: a data object declaration is none of the three contexts §8.23
// permits a type parameter to prefix the class scope resolution operator in --
// a typedef declaration, the type operator, and a type parameter assignment --
// so the subclause's own worked example, `C::T x;` written with `C` a type
// parameter, must be rejected. §6.20.3 states the type parameter case in its
// own words, so the report names that subclause, as
// TypeParamScopePrefixInExpressionIsError above establishes for the expression
// position. The prefix is bound to `int` here, so the source also provokes the
// report that the prefix does not resolve to a class; the needle below is
// contained only in the context report, which is the one this test is about.
TEST(TypeParameterElab, TypeParamScopePrefixInVarDeclIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter type C = int;\n"
      "  C::T x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type parameter 'C' may prefix the class scope resolution operator", 3,
      "6.20.3"));
}

// §6.20.3: the restriction is on the three prefix kinds §8.23 names, not on the
// declaration position. A variable whose data type is selected through an
// ordinary class name is legal wherever it is written, so it must still
// elaborate. This is what a check that rejected every scope-prefixed
// declaration would break, while still rejecting the case above.
TEST(TypeParameterElab, OrdinaryClassScopePrefixInVarDeclOk) {
  EXPECT_TRUE(
      ElabOk("class Cfg;\n"
             "  typedef int my_type;\n"
             "endclass\n"
             "module m;\n"
             "  Cfg::my_type x;\n"
             "endmodule\n"));
}

}  // namespace
