#include <gtest/gtest.h>

#include <string>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

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

TEST(TypeParameterElab, OrdinaryClassScopePrefixInVarDeclOk) {
  EXPECT_TRUE(
      ElabOk("class Cfg;\n"
             "  typedef int my_type;\n"
             "endclass\n"
             "module m;\n"
             "  Cfg::my_type x;\n"
             "endmodule\n"));
}

TEST(TypeParameterElab, ClassBoundTypeParamPrefixInTypedefOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class K;\n"
      "  typedef byte inner;\n"
      "endclass\n"
      "class P #(type C = K);\n"
      "  typedef C::inner t;\n"
      "  t z;\n"
      "endclass\n"
      "module m #(parameter type T = K);\n"
      "  typedef T::inner my_t;\n"
      "  my_t v;\n"
      "  P #(K) p;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirVariable* v = FindVar(design, "m", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 8u);
}

TEST(TypeParameterElab, ClassBoundTypeParamPrefixInTypeOperatorOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class K;\n"
      "  typedef byte inner;\n"
      "endclass\n"
      "module m #(parameter type T = K);\n"
      "  var type(T::inner) w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirVariable* w = FindVar(design, "m", "w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->width, 8u);
}

TEST(TypeParameterElab, IntBoundTypeParamPrefixInTypeParamAssignmentIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter type T = int);\n"
      "  localparam type U = T::x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type parameter 'T' used as a class scope "
                            "resolution prefix does not resolve to a class",
                            2, "6.20.3"));
}

TEST(TypeParameterElab, ClassBoundTypeParamPrefixInTypeParamAssignmentOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class K;\n"
      "  typedef byte x;\n"
      "endclass\n"
      "module m #(parameter type T = K);\n"
      "  localparam type U = T::x;\n"
      "  U u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirVariable* u = FindVar(design, "m", "u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->width, 8u);
}

TEST(TypeParameterElab, IntBoundTypeParamPrefixInTypeOperatorIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter type T = int);\n"
      "  var type(T::x) w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type parameter 'T' used as a class scope "
                            "resolution prefix does not resolve to a class",
                            2, "6.20.3"));
}

TEST(TypeParameterElab, OverrideDecidesWhetherThePrefixIsAClass) {
  const char* modules =
      "class K;\n"
      "  typedef byte inner;\n"
      "endclass\n"
      "module c #(parameter type T = int);\n"
      "  typedef T::inner my_t;\n"
      "endmodule\n"
      "module d #(parameter type T = K);\n"
      "  typedef T::inner my_t;\n"
      "endmodule\n";
  EXPECT_TRUE(ElabOk(std::string(modules) +
                     "module top; c #(K) u(); d v(); endmodule\n"));
  ElabFixture f;
  ElaborateSrc(std::string(modules) +
                   "module top; c #(K) u(); d #(int) v(); endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type parameter 'T' used as a class scope "
                            "resolution prefix does not resolve to a class",
                            8, "6.20.3"));
}

TEST(TypeParameterElab, SpecializationBindingANonClassPrefixIsError) {
  struct Form {
    const char* where;
    const char* items;
    int line;
  };
  const Form kForms[] = {
      {"module variable", "module t; P #(@) o; endmodule\n", 8},
      {"module typedef", "module t; typedef P #(@) p_t; endmodule\n", 8},
      {"unit typedef", "typedef P #(.C(@)) p_t;\nmodule t; endmodule\n", 8},
      {"class property", "class Q; P #(@) p; endclass\nmodule t; endmodule\n",
       8},
  };
  const std::string kClasses =
      "class X;\n"
      "  typedef byte T;\n"
      "endclass\n"
      "class P #(type C = X);\n"
      "  typedef C::T I;\n"
      "  localparam type J = C::T;\n"
      "endclass\n";
  for (const Form& form : kForms) {
    SCOPED_TRACE(form.where);
    std::string bad = form.items;
    std::string good = form.items;
    bad.replace(bad.find('@'), 1, "int");
    good.replace(good.find('@'), 1, "X");
    EXPECT_TRUE(ElabOk(kClasses + good));
    ElabFixture f;
    ElaborateSrc(kClasses + bad, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "type parameter 'C' used as a class scope "
                              "resolution prefix does not resolve to a class",
                              form.line, "6.20.3"));
  }
}

TEST(TypeParameterElab, DefaultSpecializationBindingANonClassPrefixIsError) {
  const std::string kBody =
      "  localparam type J = C::T;\n"
      "endclass\n"
      "module t; P o; endmodule\n";
  EXPECT_TRUE(
      ElabOk("class X; typedef byte T; endclass\n"
             "class P #(type C = X);\n" +
             kBody));
  ElabFixture f;
  ElaborateSrc(
      "class X; typedef byte T; endclass\n"
      "class P #(type C = int);\n" +
          kBody,
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type parameter 'C' used as a class scope "
                            "resolution prefix does not resolve to a class",
                            5, "6.20.3"));
}

TEST(TypeParameterElab, TypeParamPrefixInEveryPlaceMustResolveToAClass) {
  struct Place {
    const char* where;
    const char* text;
    bool takes_param;
  };
  const Place kPlaces[] = {
      {"interface",
       "interface c #(parameter type T = @);\n  %\nendinterface\n"
       "module top; c u(); endmodule\n",
       true},
      {"program",
       "program c #(parameter type T = @);\n  %\nendprogram\n"
       "module top; c u(); endmodule\n",
       true},
      {"generate block",
       "module c #(parameter type T = @);\n  if (1) begin : g %\n  end\n"
       "endmodule\nmodule top; c u(); endmodule\n",
       true},
      {"initial block",
       "module c #(parameter type T = @);\n  initial begin %\n  end\n"
       "endmodule\nmodule top; c u(); endmodule\n",
       true},
      {"function body",
       "module c #(parameter type T = @);\n"
       "  function automatic void f(); %\n  endfunction\n"
       "endmodule\nmodule top; c u(); endmodule\n",
       true},
      {"task body",
       "module c #(parameter type T = @);\n"
       "  task automatic k(); %\n  endtask\n"
       "endmodule\nmodule top; c u(); endmodule\n",
       true},
      {"function body's own type parameter",
       "module top;\n"
       "  function automatic void f(); localparam type T = @; %\n"
       "  endfunction\nendmodule\n",
       true},
      {"checker",
       "module c #(parameter type T = @);\n"
       "  checker chk; %\n  endchecker\n"
       "  chk u_chk();\nendmodule\nmodule top; c u(); endmodule\n",
       false},
      {"package",
       "package pk;\n  localparam type T = @; %\nendpackage\n"
       "module top; import pk::*; endmodule\n",
       true},
      {"compilation unit", "localparam type T = @;\n%\nmodule top; endmodule\n",
       true},
  };
  struct Use {
    const char* text;
    bool is_param;
  };
  const Use kUses[] = {{"typedef T::inner my_t;", false},
                       {"localparam type U = T::inner;", true},
                       {"var type(T::inner) w;", false}};
  const std::string kClass =
      "class K;\n"
      "  typedef byte inner;\n"
      "endclass\n";
  for (const Place& place : kPlaces) {
    for (const Use& use : kUses) {
      if (use.is_param && !place.takes_param) continue;
      SCOPED_TRACE(std::string(place.where) + ": " + use.text);
      std::string text = place.text;
      text.replace(text.find('%'), 1, use.text);
      std::string good = kClass + text;
      std::string bad = good;
      good.replace(good.find('@'), 1, "K");
      bad.replace(bad.find('@'), 1, "int");
      EXPECT_TRUE(ElabOk(good));
      ElabFixture f;
      ElaborateSrc(bad, f);
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                                "type parameter 'T' used as a class scope "
                                "resolution prefix does not resolve to a class",
                                5, "6.20.3"));
    }
  }
}

}  // namespace
