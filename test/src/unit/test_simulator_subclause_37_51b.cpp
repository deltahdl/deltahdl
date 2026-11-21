#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class PropertyDeclsEverywhere : public VpiDesignRun {
 protected:
  static vpiHandle ScopeAt(const std::string& path) {
    if (path == "$unit") return Named(vpiPackage, nullptr, "$unit");
    return By(path);
  }

  static std::vector<std::string> FormalsOf(vpiHandle decl) {
    std::vector<std::string> names;
    for (vpiHandle formal : ObjectsOf(vpiPropFormalDecl, decl)) {
      names.emplace_back(vpi_get_str(vpiName, formal));
    }
    return names;
  }

  static vpiHandle InstOf(const char* assertion) {
    vpiHandle a = Named(vpiAssertion, By("top"), assertion);
    return a == nullptr ? nullptr : vpi_handle(vpiProperty, a);
  }

  static std::vector<vpiHandle> ArgumentsOf(const char* assertion) {
    vpiHandle inst = InstOf(assertion);
    return inst == nullptr ? std::vector<vpiHandle>{}
                           : ObjectsOf(vpiArgument, inst);
  }

  static std::vector<std::string> ArgumentNamesOf(const char* assertion) {
    std::vector<std::string> names;
    for (vpiHandle argument : ArgumentsOf(assertion)) {
      const char* name = vpi_get_str(vpiName, argument);
      names.emplace_back(name == nullptr ? "" : name);
    }
    return names;
  }

  static void ExpectDeclaredAt(const std::string& scope,
                               const char* full_name) {
    vpiHandle decl = Named(vpiPropertyDecl, ScopeAt(scope), "p");
    ASSERT_NE(decl, nullptr);
    EXPECT_STREQ(vpi_get_str(vpiName, decl), "p");
    EXPECT_STREQ(vpi_get_str(vpiFullName, decl), full_name);
    EXPECT_EQ(FormalsOf(decl), std::vector<std::string>{"x"});
    vpiHandle spec = vpi_handle(vpiPropertySpec, decl);
    ASSERT_NE(spec, nullptr);
    vpiHandle expr = vpi_handle(vpiPropertyExpr, spec);
    ASSERT_NE(expr, nullptr);
    EXPECT_STREQ(vpi_get_str(vpiName, expr), "x");
  }

  static vpiHandle FormalOfP(const char* formal) {
    return Named(vpiPropFormalDecl, Named(vpiPropertyDecl, By("top"), "p"),
                 formal);
  }
};

struct DeclaringScope {
  const char* name;
  const char* src;
  const char* scope;
  const char* full_name;
};

class EveryScopeDeclaringAProperty
    : public PropertyDeclsEverywhere,
      public ::testing::WithParamInterface<DeclaringScope> {};

TEST_P(EveryScopeDeclaringAProperty, TheDeclReportsItsNamesAndSpec) {
  Run(GetParam().src);
  ExpectDeclaredAt(GetParam().scope, GetParam().full_name);
}

TEST_F(PropertyDeclsEverywhere,
       DISABLED_ACompilationUnitsDeclReportsItsNamesAndSpec) {
  Run("property p(x); x; endproperty\n"
      "module top; endmodule\n");
  ExpectDeclaredAt("$unit", "$unit::p");
}

std::string DeclaringScopeName(
    const ::testing::TestParamInfo<DeclaringScope>& info) {
  return info.param.name;
}

INSTANTIATE_TEST_SUITE_P(
    DeclaredIn, EveryScopeDeclaringAProperty,
    ::testing::Values(
        DeclaringScope{"AnInterface",
                       "interface ifc(input logic clk);\n"
                       "  property p(x); @(posedge clk) x; endproperty\n"
                       "endinterface\n"
                       "module top; logic clk; ifc i0(clk); endmodule\n",
                       "top.i0", "top.i0.p"},
        DeclaringScope{"AProgram",
                       "program prg(input logic clk);\n"
                       "  property p(x); @(posedge clk) x; endproperty\n"
                       "endprogram\n"
                       "module top; logic clk; prg pr0(clk); endmodule\n",
                       "top.pr0", "top.pr0.p"},
        DeclaringScope{"AChecker",
                       "checker chk(logic clk);\n"
                       "  property p(x); @(posedge clk) x; endproperty\n"
                       "endchecker\n"
                       "module top; logic clk; chk k0(clk); endmodule\n",
                       "top.k0", "top.k0.p"},
        DeclaringScope{"AGenerateBlock",
                       "module top; logic clk;\n"
                       "  if (1) begin : g\n"
                       "    property p(x); @(posedge clk) x; endproperty\n"
                       "  end\n"
                       "endmodule\n",
                       "top.g", "top.g.p"},
        DeclaringScope{"AClockingBlock",
                       "module top; logic clk;\n"
                       "  clocking cb @(posedge clk);\n"
                       "    property p(x); x; endproperty\n"
                       "  endclocking\n"
                       "endmodule\n",
                       "top.cb", "top.cb.p"}),
    DeclaringScopeName);

TEST_F(PropertyDeclsEverywhere, OnlyALocalVariableFormalIsAnInput) {
  Run("module top; logic clk;\n"
      "  property p(local int n, bit b, event e, sequence s, property q);\n"
      "    @(posedge clk) b;\n"
      "  endproperty\n"
      "endmodule\n");
  vpiHandle n = FormalOfP("n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(vpi_get(vpiDirection, n), vpiInput);
  for (const char* name : {"b", "e", "s", "q"}) {
    SCOPED_TRACE(name);
    vpiHandle formal = FormalOfP(name);
    ASSERT_NE(formal, nullptr);
    EXPECT_EQ(vpi_get(vpiDirection, formal), vpiNoDirection);
  }
}

TEST_F(PropertyDeclsEverywhere, ANamedEventDefaultIsReachedAsTheEvent) {
  Run("module top; logic a; event ev0;\n"
      "  property p(event ev = ev0, x = a); @(ev) x; endproperty\n"
      "endmodule\n");
  vpiHandle ev = FormalOfP("ev");
  ASSERT_NE(ev, nullptr);
  vpiHandle expr = vpi_handle(vpiExpr, ev);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(vpi_get(vpiType, expr), vpiNamedEvent);
  EXPECT_STREQ(vpi_get_str(vpiName, expr), "ev0");
}

constexpr const char* kSequenceDefaults =
    "module top; logic clk, a, b;\n"
    "  sequence sq; a ##1 b; endsequence\n"
    "  property p(s = a ##1 b, t = sq); @(posedge clk) s and t;\n"
    "  endproperty\n"
    "endmodule\n";

TEST_F(PropertyDeclsEverywhere,
       DISABLED_ASequenceExpressionDefaultIsReachedAsAnOperation) {
  Run(kSequenceDefaults);
  vpiHandle s = vpi_handle(vpiExpr, FormalOfP("s"));
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(vpi_get(vpiType, s), vpiOperation);
}

TEST_F(PropertyDeclsEverywhere,
       DISABLED_ADeclaredSequenceDefaultIsReachedAsItsInst) {
  Run(kSequenceDefaults);
  vpiHandle t = vpi_handle(vpiExpr, FormalOfP("t"));
  ASSERT_NE(t, nullptr);
  EXPECT_EQ(vpi_get(vpiType, t), vpiSequenceInst);
}

TEST_F(PropertyDeclsEverywhere, DISABLED_NamedActualsComeBackInFormalOrder) {
  Run("module top; logic clk, a, c;\n"
      "  property p(x, y); @(posedge clk) x |-> y; endproperty\n"
      "  a1: assert property (p(.y(c), .x(a)));\n"
      "endmodule\n");
  EXPECT_EQ(ArgumentNamesOf("a1"), (std::vector<std::string>{"a", "c"}));
}

TEST_F(PropertyDeclsEverywhere, AnActualOverridesTheFormalsDefault) {
  Run("module top; logic clk, a, b, c;\n"
      "  property p(x, y = b); @(posedge clk) x |-> y; endproperty\n"
      "  a1: assert property (p(a, c));\n"
      "  a2: assert property (p(a));\n"
      "endmodule\n");
  EXPECT_EQ(ArgumentNamesOf("a1"), (std::vector<std::string>{"a", "c"}));
  EXPECT_EQ(ArgumentNamesOf("a2"), (std::vector<std::string>{"a", "b"}));
}

TEST_F(PropertyDeclsEverywhere, ANamedEventActualIsReachedAsTheEvent) {
  Run("module top; logic a; event ev;\n"
      "  property p(event e, x); @(e) x; endproperty\n"
      "  a1: assert property (p(ev, a));\n"
      "endmodule\n");
  const std::vector<vpiHandle> kArguments = ArgumentsOf("a1");
  ASSERT_EQ(kArguments.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kArguments[0]), vpiNamedEvent);
  EXPECT_STREQ(vpi_get_str(vpiName, kArguments[0]), "ev");
  EXPECT_STREQ(vpi_get_str(vpiName, kArguments[1]), "a");
}

TEST_F(PropertyDeclsEverywhere, APropertyActualIsReachedInItsFormalsPlace) {
  Run("module top; logic clk, a, b;\n"
      "  default clocking cb @(posedge clk); endclocking\n"
      "  property q(property r, x); r and x; endproperty\n"
      "  a1: assert property (q(a |-> b, a));\n"
      "endmodule\n");
  const std::vector<vpiHandle> kArguments = ArgumentsOf("a1");
  ASSERT_EQ(kArguments.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kArguments[0]), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, kArguments[0]), vpiOverlapImplyOp);
  EXPECT_STREQ(vpi_get_str(vpiName, kArguments[1]), "a");
}

TEST_F(PropertyDeclsEverywhere, DISABLED_APackageScopedInstanceReachesItsDecl) {
  Run("package pk; property p(c, x); @(posedge c) x; endproperty\n"
      "endpackage\n"
      "module top; logic clk, a;\n"
      "  a1: assert property (pk::p(clk, a));\n"
      "endmodule\n");
  vpiHandle inst = InstOf("a1");
  ASSERT_NE(inst, nullptr);
  vpiHandle decl = vpi_handle(vpiPropertyDecl, inst);
  ASSERT_NE(decl, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, decl), "pk::p");
}

TEST_F(PropertyDeclsEverywhere, AnAssumedAndACoveredInstanceReachTheirDecl) {
  Run("module top; logic clk, a;\n"
      "  property p(x); @(posedge clk) x; endproperty\n"
      "  s1: assume property (p(a));\n"
      "  c1: cover property (p(a));\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(decl, nullptr);
  for (const char* name : {"s1", "c1"}) {
    SCOPED_TRACE(name);
    vpiHandle inst = InstOf(name);
    ASSERT_NE(inst, nullptr);
    EXPECT_EQ(vpi_get(vpiType, inst), vpiPropertyInst);
    EXPECT_TRUE(vpi_compare_objects(vpi_handle(vpiPropertyDecl, inst), decl));
  }
}

TEST_F(PropertyDeclsEverywhere, FormalsOfMixedKindsIterateAsWritten) {
  Run("module top; logic clk, a;\n"
      "  property p(int n, x, local input int m, y = a);\n"
      "    @(posedge clk) x;\n"
      "  endproperty\n"
      "  property q(local input int m, int n, x, y = a);\n"
      "    @(posedge clk) x;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_EQ(FormalsOf(Named(vpiPropertyDecl, By("top"), "p")),
            (std::vector<std::string>{"n", "x", "m", "y"}));
  EXPECT_EQ(FormalsOf(Named(vpiPropertyDecl, By("top"), "q")),
            (std::vector<std::string>{"m", "n", "x", "y"}));
}

TEST_F(PropertyDeclsEverywhere, APropertyWithoutFormalsOrLocalsIteratesNone) {
  Run("module top; logic clk, a;\n"
      "  property p; @(posedge clk) a; endproperty\n"
      "  property q(); @(posedge clk) a; endproperty\n"
      "endmodule\n");
  for (const char* name : {"p", "q"}) {
    SCOPED_TRACE(name);
    vpiHandle decl = Named(vpiPropertyDecl, By("top"), name);
    ASSERT_NE(decl, nullptr);
    EXPECT_EQ(vpi_iterate(vpiPropFormalDecl, decl), nullptr);
    EXPECT_EQ(vpi_iterate(vpiVariables, decl), nullptr);
  }
}

TEST_F(PropertyDeclsEverywhere, AnInstWithNoDisableIffHasNoCondition) {
  Run("module top; logic clk, a;\n"
      "  property p(x); @(posedge clk) x; endproperty\n"
      "  a1: assert property (p(a));\n"
      "endmodule\n");
  vpiHandle inst = InstOf("a1");
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(vpi_handle(vpiDisableCondition, inst), nullptr);
}

TEST_F(PropertyDeclsEverywhere, FormalTypespecsOfARun) {
  Run("class D; typedef bit m_t [int]; endclass\n"
      "module top; logic clk;\n"
      "  property p(x, D::m_t z, local input int n);\n"
      "    @(posedge clk) x;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(FormalOfP("x"), nullptr);
  EXPECT_EQ(vpi_handle(vpiTypespec, FormalOfP("x")), nullptr);
  vpiHandle z = vpi_handle(vpiTypespec, FormalOfP("z"));
  ASSERT_NE(z, nullptr);
  EXPECT_EQ(vpi_get(vpiArrayType, z), vpiAssocArray);
  vpiHandle index = vpi_handle(vpiIndexTypespec, z);
  ASSERT_NE(index, nullptr);
  EXPECT_EQ(vpi_get(vpiType, index), vpiIntTypespec);
  vpiHandle n = vpi_handle(vpiTypespec, FormalOfP("n"));
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(vpi_get(vpiType, n), vpiIntTypespec);
}

}  // namespace
}  // namespace delta
