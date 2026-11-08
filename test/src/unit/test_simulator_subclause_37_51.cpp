#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(PropertyDeclModel, PropFormalDeclIterationFollowsDeclarationOrder) {
  VpiContext ctx;
  VpiObject decl;
  decl.type = vpiPropertyDecl;
  VpiObject spec;
  spec.type = vpiPropertySpec;
  VpiObject f0;
  f0.type = vpiPropFormalDecl;
  VpiObject f1;
  f1.type = vpiPropFormalDecl;
  decl.children = {&f0, &spec, &f1};

  auto formals = VpiPropFormals(&decl);
  ASSERT_EQ(formals.size(), 2u);
  EXPECT_EQ(formals[0], &f0);
  EXPECT_EQ(formals[1], &f1);

  VpiHandle it = ctx.Iterate(vpiPropFormalDecl, &decl);
  ASSERT_NE(it, nullptr);
  std::vector<VpiHandle> seen;
  while (VpiHandle h = ctx.Scan(it)) seen.push_back(h);
  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], &f0);
  EXPECT_EQ(seen[1], &f1);
}

TEST(PropertyDeclModel, NullDeclarationHasNoFormals) {
  EXPECT_TRUE(VpiPropFormals(nullptr).empty());
}

TEST(PropertyDeclModel, ArgumentsFollowFormalOrderAndFillDefaults) {
  VpiObject a0;
  VpiObject a2;
  VpiObject def1;

  std::vector<VpiPropertyFormal> formals = {
      {nullptr},
      {&def1},
      {nullptr},
  };
  std::vector<VpiHandle> provided = {&a0, nullptr, &a2};

  auto args = VpiPropertyInstArguments(formals, provided);
  ASSERT_EQ(args.size(), 3u);
  EXPECT_EQ(args[0], &a0);
  EXPECT_EQ(args[1], &def1);
  EXPECT_EQ(args[2], &a2);
}

TEST(PropertyDeclModel, ArgumentsPreferActualsAndDefaultTrailingFormals) {
  VpiObject a0;
  VpiObject def1;

  std::vector<VpiPropertyFormal> formals = {{nullptr}, {&def1}};

  auto supplied = VpiPropertyInstArguments(formals, {&a0, &def1});
  ASSERT_EQ(supplied.size(), 2u);
  EXPECT_EQ(supplied[1], &def1);

  auto trailing = VpiPropertyInstArguments(formals, {&a0});
  ASSERT_EQ(trailing.size(), 2u);
  EXPECT_EQ(trailing[0], &a0);
  EXPECT_EQ(trailing[1], &def1);
}

TEST(PropertyDeclModel, FormalTypespecReportsNullWhenUntyped) {
  VpiObject typed;
  typed.type = vpiPropFormalDecl;
  VpiObject ts;
  ts.type = vpiTypespec;
  typed.children = {&ts};
  EXPECT_EQ(VpiPropFormalTypespec(&typed), &ts);

  VpiObject untyped;
  untyped.type = vpiPropFormalDecl;
  EXPECT_EQ(VpiPropFormalTypespec(&untyped), nullptr);
  EXPECT_EQ(VpiPropFormalTypespec(nullptr), nullptr);
}

TEST(PropertyDeclModel, FormalInitExprReachesNamedEventOrPropertyExpr) {
  VpiObject with_event;
  with_event.type = vpiPropFormalDecl;
  VpiObject ev;
  ev.type = vpiNamedEvent;
  with_event.children = {&ev};
  EXPECT_EQ(VpiPropFormalInitExpr(&with_event), &ev);

  VpiObject with_prop_expr;
  with_prop_expr.type = vpiPropFormalDecl;
  VpiObject pe;
  pe.type = vpiClockedProp;
  with_prop_expr.children = {&pe};
  EXPECT_EQ(VpiPropFormalInitExpr(&with_prop_expr), &pe);

  VpiObject untyped_only;
  untyped_only.type = vpiPropFormalDecl;
  VpiObject ts;
  ts.type = vpiTypespec;
  untyped_only.children = {&ts};
  EXPECT_EQ(VpiPropFormalInitExpr(&untyped_only), nullptr);
}

TEST(PropertyDeclModel, FormalDirectionDistinguishesLocalVariableArguments) {
  EXPECT_EQ(VpiPropFormalDirection(true), vpiInput);
  EXPECT_EQ(VpiPropFormalDirection(false), vpiNoDirection);
}

TEST(PropertyDeclModel, PropertyInstResolvesItsDeclaration) {
  VpiObject inst;
  inst.type = vpiPropertyInst;
  VpiObject decl;
  decl.type = vpiPropertyDecl;
  inst.property_decl = &decl;
  EXPECT_EQ(VpiPropertyInstDecl(&inst), &decl);

  VpiObject lone;
  lone.type = vpiPropertyInst;
  EXPECT_EQ(VpiPropertyInstDecl(&lone), nullptr);
  EXPECT_EQ(VpiPropertyInstDecl(nullptr), nullptr);
}

TEST(PropertyDeclModel, PropertyArgumentKindsAreNamedEventOrPropertyExpr) {
  EXPECT_TRUE(VpiIsPropertyArgumentType(vpiNamedEvent));
  EXPECT_TRUE(VpiIsPropertyArgumentType(vpiClockedProp));
  EXPECT_TRUE(VpiIsPropertyArgumentType(vpiCaseProperty));
  EXPECT_TRUE(VpiIsPropertyArgumentType(vpiPropertyInst));

  EXPECT_FALSE(VpiIsPropertyArgumentType(vpiNet));
  EXPECT_FALSE(VpiIsPropertyArgumentType(vpiModule));
}

TEST(PropertyDeclModel, PropertyInstDisableConditionReachesAnExpression) {
  EXPECT_TRUE(VpiIsDisableConditionType(vpiExpr));
  EXPECT_TRUE(VpiIsDisableConditionType(vpiOperation));
  EXPECT_FALSE(VpiIsDisableConditionType(vpiModule));
}

TEST(PropertyDeclModel, PropertyDeclReachesItsSpecification) {
  VpiContext ctx;
  VpiObject decl;
  decl.type = vpiPropertyDecl;
  VpiObject spec;
  spec.type = vpiPropertySpec;
  decl.children = {&spec};

  EXPECT_EQ(ctx.Handle(vpiPropertySpec, &decl), &spec);
}

TEST(PropertyDeclModel, PropertyDeclAndFormalReportTheirNames) {
  VpiContext ctx;
  VpiObject decl;
  decl.type = vpiPropertyDecl;
  decl.name = "chk";
  decl.full_name = "top.chk";
  EXPECT_STREQ(ctx.GetStr(vpiName, &decl), "chk");
  EXPECT_STREQ(ctx.GetStr(vpiFullName, &decl), "top.chk");

  VpiObject formal;
  formal.type = vpiPropFormalDecl;
  formal.name = "a";
  EXPECT_STREQ(ctx.GetStr(vpiName, &formal), "a");
  EXPECT_STREQ(ctx.GetStr(vpiFullName, &formal), "a");
}

class PropertyDeclsOfARun : public VpiDesignRun {
 protected:
  static std::string NameReached(int relation, vpiHandle ref) {
    vpiHandle reached = ref == nullptr ? nullptr : vpi_handle(relation, ref);
    return reached == nullptr ? "" : vpi_get_str(vpiName, reached);
  }

  static vpiHandle ClassTypespecOfH() {
    vpiHandle decl = Named(vpiPropertyDecl, By("top"), "p");
    vpiHandle h =
        decl == nullptr
            ? nullptr
            : vpi_handle(vpiTypespec, Named(vpiPropFormalDecl, decl, "h"));
    if (h == nullptr || vpi_get(vpiType, h) != vpiClassTypespec ||
        std::string(vpi_get_str(vpiName, h)) != "C") {
      return nullptr;
    }
    return h;
  }

  static std::vector<vpiHandle> ArgumentsOf(const char* assertion) {
    std::vector<vpiHandle> arguments;
    vpiHandle a = Named(vpiAssertion, By("top"), assertion);
    vpiHandle inst = a == nullptr ? nullptr : vpi_handle(vpiProperty, a);
    vpiHandle it = inst == nullptr ? nullptr : vpi_iterate(vpiArgument, inst);
    if (it == nullptr) return arguments;
    for (vpiHandle h = vpi_scan(it); h != nullptr; h = vpi_scan(it)) {
      arguments.push_back(h);
    }
    return arguments;
  }

  static std::string EventActualsSource(const std::vector<std::string>& specs) {
    std::string src =
        "module top; logic clk, a;\n"
        "  property p(event e, x); @(e) x; endproperty\n";
    for (size_t i = 0; i < specs.size(); ++i) {
      src += "  a" + std::to_string(i + 1) + ": assert property (" + specs[i] +
             ");\n";
    }
    return src + "endmodule\n";
  }

  static int FirstArgumentOp(const char* assertion) {
    const std::vector<vpiHandle> kArguments = ArgumentsOf(assertion);
    return kArguments.size() == 2 ? vpi_get(vpiOpType, kArguments[0]) : 0;
  }

  static std::vector<std::string> NamesOf(int relation, vpiHandle ref) {
    std::vector<std::string> names;
    vpiHandle it = vpi_iterate(relation, ref);
    if (it == nullptr) return names;
    for (vpiHandle h = vpi_scan(it); h != nullptr; h = vpi_scan(it)) {
      names.emplace_back(vpi_get_str(vpiName, h));
    }
    return names;
  }
};

TEST_F(PropertyDeclsOfARun, AnInstanceReachesThePropertyItDeclares) {
  Run("module top; logic clk, rst, a, b;\n"
      "  property p(x, y = b);\n"
      "    @(posedge clk) disable iff (rst) a;\n"
      "  endproperty\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(decl, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, decl), "top.p");
  EXPECT_EQ(NamesOf(vpiPropFormalDecl, decl),
            (std::vector<std::string>{"x", "y"}));
  vpiHandle y = Named(vpiPropFormalDecl, decl, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(vpi_get(vpiDirection, y), vpiNoDirection);
  EXPECT_EQ(NameReached(vpiExpr, y), "b");
  EXPECT_EQ(NameReached(vpiExpr, Named(vpiPropFormalDecl, decl, "x")), "");
  vpiHandle spec = vpi_handle(vpiPropertySpec, decl);
  ASSERT_NE(spec, nullptr);
  EXPECT_NE(vpi_handle(vpiClockingEvent, spec), nullptr);
  EXPECT_EQ(NameReached(vpiDisableCondition, spec), "rst");
  EXPECT_EQ(NameReached(vpiPropertyExpr, spec), "a");
}

TEST_F(PropertyDeclsOfARun, AGenerateBlockReachesThePropertyItDeclares) {
  Run("module top; logic clk, a;\n"
      "  for (genvar i = 0; i < 1; i++) begin : g\n"
      "    property q; @(posedge clk) a; endproperty\n"
      "  end\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top.g[0]"), "q");
  ASSERT_NE(decl, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, decl), "top.g[0].q");
  EXPECT_EQ(Named(vpiPropertyDecl, By("top"), "q"), nullptr);
}

TEST_F(PropertyDeclsOfARun, AnAssertionReachesThePropertyInstItWrites) {
  Run("module top; logic clk, a, b;\n"
      "  property p(x, y = b); @(posedge clk) x; endproperty\n"
      "  a1: assert property (p(a));\n"
      "endmodule\n");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  ASSERT_NE(a1, nullptr);
  vpiHandle inst = vpi_handle(vpiProperty, a1);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(vpi_get(vpiType, inst), vpiPropertyInst);
  vpiHandle decl = vpi_handle(vpiPropertyDecl, inst);
  ASSERT_NE(decl, nullptr);
  EXPECT_TRUE(
      vpi_compare_objects(decl, Named(vpiPropertyDecl, By("top"), "p")));
  EXPECT_EQ(NamesOf(vpiArgument, inst), (std::vector<std::string>{"a", "b"}));
}

TEST_F(PropertyDeclsOfARun, AProceduralAssertionReachesItsPropertyInst) {
  Run("module top; logic clk, a;\n"
      "  property p(x); x; endproperty\n"
      "  always @(posedge clk) p1: assert property (p(a));\n"
      "endmodule\n");
  vpiHandle p1 = Named(vpiAssertion, By("top"), "p1");
  ASSERT_NE(p1, nullptr);
  vpiHandle inst = vpi_handle(vpiProperty, p1);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(vpi_get(vpiType, inst), vpiPropertyInst);
  EXPECT_EQ(NameReached(vpiPropertyDecl, inst), "p");
  EXPECT_EQ(NamesOf(vpiArgument, inst), (std::vector<std::string>{"a"}));
}

TEST_F(PropertyDeclsOfARun, APropertyInstReachesItsDisableCondition) {
  Run("module top; logic clk, rst, a, b;\n"
      "  default disable iff rst;\n"
      "  property p(x); @(posedge clk) x; endproperty\n"
      "  property q(x, r); @(posedge clk) disable iff (r) x; endproperty\n"
      "  a1: assert property (p(a));\n"
      "  a2: assert property (q(a, b));\n"
      "  always @(posedge clk) p1: assert property (p(a));\n"
      "endmodule\n");
  const auto kConditionOf = [](const char* name) {
    vpiHandle assertion = Named(vpiAssertion, By("top"), name);
    return NameReached(
        vpiDisableCondition,
        assertion == nullptr ? nullptr : vpi_handle(vpiProperty, assertion));
  };
  EXPECT_EQ(kConditionOf("a1"), "rst");
  EXPECT_EQ(kConditionOf("a2"), "b");
  EXPECT_EQ(kConditionOf("p1"), "rst");
}

TEST_F(PropertyDeclsOfARun, ATypedFormalReachesItsTypespec) {
  Run("module top; logic clk;\n"
      "  property p(bit x, untyped y, event e, sequence s, property q,\n"
      "             realtime t);\n"
      "    @(posedge clk) x;\n"
      "  endproperty\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(decl, nullptr);
  const auto kTypespecOf = [decl](const char* formal) {
    vpiHandle ts =
        vpi_handle(vpiTypespec, Named(vpiPropFormalDecl, decl, formal));
    return ts == nullptr ? 0 : vpi_get(vpiType, ts);
  };
  EXPECT_EQ(kTypespecOf("x"), vpiBitTypespec);
  EXPECT_EQ(kTypespecOf("y"), 0);
  EXPECT_EQ(kTypespecOf("e"), vpiEventTypespec);
  EXPECT_EQ(kTypespecOf("s"), vpiSequenceTypespec);
  EXPECT_EQ(kTypespecOf("q"), vpiPropertyTypespec);
  EXPECT_EQ(kTypespecOf("t"), vpiRealTypespec);
}

TEST_F(PropertyDeclsOfARun, ALocalVariableFormalIsAnInput) {
  Run("module top; logic clk, a;\n"
      "  property p(x, local input int n);\n"
      "    @(posedge clk) x;\n"
      "  endproperty\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(decl, nullptr);
  vpiHandle n = Named(vpiPropFormalDecl, decl, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(vpi_get(vpiDirection, n), vpiInput);
  vpiHandle x = Named(vpiPropFormalDecl, decl, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(vpi_get(vpiDirection, x), vpiNoDirection);
}

TEST_F(PropertyDeclsOfARun, AnInstReachesItsPropertyPastAnother) {
  Run("module top; logic clk, a, b;\n"
      "  property p1; @(posedge clk) a; endproperty\n"
      "  property p2; @(posedge clk) b; endproperty\n"
      "  a2: assert property (p2);\n"
      "endmodule\n");
  vpiHandle a2 = Named(vpiAssertion, By("top"), "a2");
  ASSERT_NE(a2, nullptr);
  vpiHandle inst = vpi_handle(vpiProperty, a2);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(NameReached(vpiPropertyDecl, inst), "p2");
}

TEST_F(PropertyDeclsOfARun, APropertyReachesItsLocalVariables) {
  Run("module top; logic clk, a;\n"
      "  property p;\n"
      "    int n; bit f;\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(decl, nullptr);
  EXPECT_EQ(NamesOf(vpiVariables, decl), (std::vector<std::string>{"n", "f"}));
  EXPECT_EQ(KindsOf(vpiVariables, decl),
            (std::vector<int>{vpiIntVar, vpiBitVar}));
  vpiHandle n = Named(vpiVariables, decl, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, n), "top.p.n");
}

TEST_F(PropertyDeclsOfARun, APropertyReachesAPackedLocalVariableAndItsSpec) {
  Run("module top; logic clk, a;\n"
      "  property p; logic [3:0] v; @(posedge clk) a; endproperty\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(decl, nullptr);
  EXPECT_EQ(KindsOf(vpiVariables, decl), (std::vector<int>{vpiLogicVar}));
  EXPECT_NE(Named(vpiVariables, decl, "v"), nullptr);
  vpiHandle spec = vpi_handle(vpiPropertySpec, decl);
  ASSERT_NE(spec, nullptr);
  EXPECT_NE(vpi_handle(vpiClockingEvent, spec), nullptr);
  EXPECT_EQ(NameReached(vpiPropertyExpr, spec), "a");
}

TEST_F(PropertyDeclsOfARun, APropertyReachesALocalOfATypeName) {
  Run("module top; logic clk, a;\n"
      "  typedef logic [3:0] nib_t;\n"
      "  property p; nib_t v; @(posedge clk) a; endproperty\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(decl, nullptr);
  EXPECT_EQ(KindsOf(vpiVariables, decl), (std::vector<int>{vpiLogicVar}));
  EXPECT_NE(vpi_handle(vpiPropertySpec, decl), nullptr);
}

TEST_F(PropertyDeclsOfARun, AClockingBlockReachesThePropertyItDeclares) {
  Run("module top; logic clk, a;\n"
      "  clocking cb @(posedge clk);\n"
      "    property p; a; endproperty\n"
      "  endclocking\n"
      "  a1: assert property (cb.p);\n"
      "endmodule\n");
  vpiHandle cb = Named(vpiClockingBlock, By("top"), "cb");
  ASSERT_NE(cb, nullptr);
  vpiHandle decl = Named(vpiPropertyDecl, cb, "p");
  ASSERT_NE(decl, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, decl), "top.cb.p");
  EXPECT_EQ(Named(vpiPropertyDecl, By("top"), "p"), nullptr);
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  ASSERT_NE(a1, nullptr);
  vpiHandle inst = vpi_handle(vpiProperty, a1);
  ASSERT_NE(inst, nullptr);
  EXPECT_TRUE(vpi_compare_objects(vpi_handle(vpiPropertyDecl, inst), decl));
}

TEST_F(PropertyDeclsOfARun, AnInstThroughAnInterfaceReachesItsProperty) {
  Run("interface ifc(input logic clk); logic a;\n"
      "  property p; @(posedge clk) a; endproperty\n"
      "endinterface\n"
      "module top; logic clk; ifc i0(clk);\n"
      "  a1: assert property (i0.p);\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top.i0"), "p");
  ASSERT_NE(decl, nullptr);
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  ASSERT_NE(a1, nullptr);
  vpiHandle inst = vpi_handle(vpiProperty, a1);
  ASSERT_NE(inst, nullptr);
  EXPECT_TRUE(vpi_compare_objects(vpi_handle(vpiPropertyDecl, inst), decl));
}

TEST_F(PropertyDeclsOfARun, AFormalOfAWrittenTypeReachesItsTypespec) {
  Run("typedef logic [7:0] byte_t;\n"
      "module top; logic clk;\n"
      "  typedef struct packed { logic a, b; } pair_t;\n"
      "  property p(bit [3:0] v, pair_t s, byte_t w);\n"
      "    @(posedge clk) v[0];\n"
      "  endproperty\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(decl, nullptr);
  vpiHandle v = vpi_handle(vpiTypespec, Named(vpiPropFormalDecl, decl, "v"));
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(vpi_get(vpiType, v), vpiBitTypespec);
  vpiHandle ranges = vpi_iterate(vpiRange, v);
  ASSERT_NE(ranges, nullptr);
  vpiHandle range = vpi_scan(ranges);
  ASSERT_NE(range, nullptr);
  EXPECT_EQ(vpi_get(vpiSize, range), 4);
  vpiHandle s = vpi_handle(vpiTypespec, Named(vpiPropFormalDecl, decl, "s"));
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(vpi_get(vpiType, s), vpiStructTypespec);
  EXPECT_STREQ(vpi_get_str(vpiName, s), "pair_t");
  vpiHandle w = vpi_handle(vpiTypespec, Named(vpiPropFormalDecl, decl, "w"));
  ASSERT_NE(w, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, w), "byte_t");
}

TEST_F(PropertyDeclsOfARun, ADollarActualIsTheUnboundedConstant) {
  Run("module top; logic clk, a, b;\n"
      "  property p(x = b, y); @(posedge clk) x; endproperty\n"
      "  a1: assert property (p(, $));\n"
      "endmodule\n");
  const std::vector<vpiHandle> kArguments = ArgumentsOf("a1");
  ASSERT_EQ(kArguments.size(), 2U);
  EXPECT_STREQ(vpi_get_str(vpiName, kArguments[0]), "b");
  EXPECT_EQ(vpi_get(vpiType, kArguments[1]), vpiConstant);
  EXPECT_EQ(vpi_get(vpiConstType, kArguments[1]), vpiUnboundedConst);
}

TEST_F(PropertyDeclsOfARun, ASequenceActualIsItsPropertyExpr) {
  Run("module top; logic clk, a, b, c;\n"
      "  property p(s, x); @(posedge clk) s |-> x; endproperty\n"
      "  a1: assert property (p(a ##1 b, c));\n"
      "endmodule\n");
  const std::vector<vpiHandle> kArguments = ArgumentsOf("a1");
  ASSERT_EQ(kArguments.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kArguments[0]), vpiOperation);
  EXPECT_STREQ(vpi_get_str(vpiName, kArguments[1]), "c");
}

TEST_F(PropertyDeclsOfARun, AnInstThroughAUnitImportReachesItsProperty) {
  Run("package pk; property p(c, x); @(posedge c) x; endproperty\n"
      "endpackage\n"
      "import pk::*;\n"
      "module top; logic clk, a;\n"
      "  a1: assert property (p(clk, a));\n"
      "endmodule\n");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_STREQ(
      vpi_get_str(vpiFullName,
                  vpi_handle(vpiPropertyDecl, vpi_handle(vpiProperty, a1))),
      "pk::p");
}

TEST_F(PropertyDeclsOfARun, AFormalOfAnImportedTypedefReachesItsTypespec) {
  Run("package pk; typedef logic [3:0] nib_t; typedef int word_t;\n"
      "endpackage\n"
      "package qk; typedef bit flag_t; endpackage\n"
      "module top; import qk::*; import pk::word_t; import pk::nib_t;\n"
      "  logic clk;\n"
      "  property p(nib_t v); @(posedge clk) v[0]; endproperty\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(decl, nullptr);
  vpiHandle v = vpi_handle(vpiTypespec, Named(vpiPropFormalDecl, decl, "v"));
  ASSERT_NE(v, nullptr);
  EXPECT_TRUE(vpi_compare_objects(v, Named(vpiTypedef, By("pk"), "nib_t")));
}

TEST_F(PropertyDeclsOfARun, AFormalOfAPackagesTypeReachesItsTypespec) {
  Run("typedef bit [5:0] t;\n"
      "package pk; typedef logic [1:0] t; endpackage\n"
      "module top; logic clk;\n"
      "  property p(pk::t v); @(posedge clk) v[0]; endproperty\n"
      "endmodule\n");
  vpiHandle v = vpi_handle(
      vpiTypespec,
      Named(vpiPropFormalDecl, Named(vpiPropertyDecl, By("top"), "p"), "v"));
  EXPECT_TRUE(vpi_compare_objects(v, Named(vpiTypedef, By("pk"), "t")));
}

TEST_F(PropertyDeclsOfARun, AFormalOfAnAliasTypedefReachesItsTypespec) {
  Run("module top; logic clk;\n"
      "  typedef logic [3:0] nib_t; typedef nib_t half_t;\n"
      "  property p(half_t v); @(posedge clk) v[0]; endproperty\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(decl, nullptr);
  vpiHandle v = vpi_handle(vpiTypespec, Named(vpiPropFormalDecl, decl, "v"));
  ASSERT_NE(v, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, v), "half_t");
}

TEST_F(PropertyDeclsOfARun, AFormalOfAModulesClassReachesItsClassTypespec) {
  Run("module top; logic clk;\n"
      "  class D; endclass\n"
      "  class C; endclass\n"
      "  property p(C h); @(posedge clk) 1; endproperty\n"
      "endmodule\n");
  vpiHandle h = ClassTypespecOfH();
  ASSERT_NE(h, nullptr);
  EXPECT_TRUE(vpi_compare_objects(vpi_handle(vpiClassDefn, h),
                                  Named(vpiClassDefn, By("top"), "C")));
}

TEST_F(PropertyDeclsOfARun, AFormalOfAUnitsClassReachesItsClassTypespec) {
  Run("class C; endclass\n"
      "module top; logic clk;\n"
      "  property p(C h); @(posedge clk) 1; endproperty\n"
      "endmodule\n");
  EXPECT_NE(ClassTypespecOfH(), nullptr);
}

TEST_F(PropertyDeclsOfARun, AnActualOfATypedFormalIsBuiltAgainstItsTypespec) {
  Run("module top; logic clk, x;\n"
      "  typedef struct packed { logic a, b; } pair_t;\n"
      "  property p(pair_t s); @(posedge clk) 1; endproperty\n"
      "  a1: assert property (p('{x, 1'b0}));\n"
      "endmodule\n");
  const std::vector<vpiHandle> kArguments = ArgumentsOf("a1");
  ASSERT_EQ(kArguments.size(), 1U);
  EXPECT_EQ(vpi_get(vpiOpType, kArguments[0]), vpiAssignmentPatternOp);
  vpiHandle it = vpi_iterate(vpiOperand, kArguments[0]);
  ASSERT_NE(it, nullptr);
  vpiHandle first = vpi_scan(it);
  ASSERT_NE(first, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, first), "x");
}

TEST_F(PropertyDeclsOfARun, AKeyedPatternActualTakesItsFormalsOrder) {
  Run("module top; logic clk, x;\n"
      "  typedef struct packed { logic a, b; } pair_t;\n"
      "  property p(pair_t s); @(posedge clk) 1; endproperty\n"
      "  a1: assert property (p('{b: x, default: 1'b0}));\n"
      "endmodule\n");
  const std::vector<vpiHandle> kArguments = ArgumentsOf("a1");
  ASSERT_EQ(kArguments.size(), 1U);
  EXPECT_EQ(vpi_get(vpiOpType, kArguments[0]), vpiAssignmentPatternOp);
  vpiHandle it = vpi_iterate(vpiOperand, kArguments[0]);
  ASSERT_NE(it, nullptr);
  vpiHandle first = vpi_scan(it);
  ASSERT_NE(first, nullptr);
  EXPECT_EQ(vpi_get(vpiType, first), vpiConstant);
  vpiHandle second = vpi_scan(it);
  ASSERT_NE(second, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, second), "x");
}

TEST_F(PropertyDeclsOfARun, AnEdgeEventActualIsAnEdgeOperation) {
  Run("module top; logic clk, a;\n"
      "  property p(event e, x); @(e) x; endproperty\n"
      "  a1: assert property (p(posedge clk, a));\n"
      "endmodule\n");
  const std::vector<vpiHandle> kArguments = ArgumentsOf("a1");
  ASSERT_EQ(kArguments.size(), 2U);
  EXPECT_EQ(vpi_get(vpiOpType, kArguments[0]), vpiPosedgeOp);
}

TEST_F(PropertyDeclsOfARun, AnOrEventActualIsAnEventOrOperation) {
  Run("module top; logic clk, a;\n"
      "  property p(event e, x); @(e) x; endproperty\n"
      "  a1: assert property (p(negedge clk or posedge clk, a));\n"
      "endmodule\n");
  const std::vector<vpiHandle> kArguments = ArgumentsOf("a1");
  ASSERT_EQ(kArguments.size(), 2U);
  EXPECT_EQ(vpi_get(vpiOpType, kArguments[0]), vpiEventOrOp);
}

TEST_F(PropertyDeclsOfARun, AnIffEventActualIsAnIffOperation) {
  Run("module top; logic clk, a;\n"
      "  property p(event e, x); @(e) x; endproperty\n"
      "  a1: assert property (p(posedge clk iff a, a));\n"
      "endmodule\n");
  const std::vector<vpiHandle> kArguments = ArgumentsOf("a1");
  ASSERT_EQ(kArguments.size(), 2U);
  EXPECT_EQ(vpi_get(vpiOpType, kArguments[0]), vpiIffOp);
}

TEST_F(PropertyDeclsOfARun, AnEdgeAndAnOrEventActualOfOneProperty) {
  Run(EventActualsSource(
      {"p(posedge clk, a)", "p(negedge clk or posedge clk, a)"}));
  EXPECT_EQ(FirstArgumentOp("a1"), vpiPosedgeOp);
  EXPECT_EQ(FirstArgumentOp("a2"), vpiEventOrOp);
}

TEST_F(PropertyDeclsOfARun, AnOrAndAnIffEventActualOfOneProperty) {
  Run(EventActualsSource(
      {"p(negedge clk or posedge clk, a)", "p(posedge clk iff a, a)"}));
  EXPECT_EQ(FirstArgumentOp("a1"), vpiEventOrOp);
  EXPECT_EQ(FirstArgumentOp("a2"), vpiIffOp);
}

TEST_F(PropertyDeclsOfARun, AnEdgeAndAnIffEventActualOfOneProperty) {
  Run(EventActualsSource({"p(posedge clk, a)", "p(posedge clk iff a, a)"}));
  EXPECT_EQ(FirstArgumentOp("a1"), vpiPosedgeOp);
  EXPECT_EQ(FirstArgumentOp("a2"), vpiIffOp);
}

TEST_F(PropertyDeclsOfARun, AnEdgeAnOrAndAnIffEventActualOfOneProperty) {
  Run(EventActualsSource({"p(posedge clk, a)",
                          "p(negedge clk or posedge clk, a)",
                          "p(posedge clk iff a, a)"}));
  EXPECT_EQ(FirstArgumentOp("a1"), vpiPosedgeOp);
  EXPECT_EQ(FirstArgumentOp("a2"), vpiEventOrOp);
  EXPECT_EQ(FirstArgumentOp("a3"), vpiIffOp);
}

TEST_F(PropertyDeclsOfARun,
       TheNamedAssertionsOfAnInstancePassItsPropertyInsts) {
  Run(EventActualsSource({"p(posedge clk, a)", "p(posedge clk, a)"}));
  EXPECT_EQ(VpiDesignRun::NamesOf(vpiAssertion, By("top")),
            (std::vector<std::string>{"a1", "a2"}));
}

TEST_F(PropertyDeclsOfARun, TwoInstancesPassingOneEdgeEachReachIt) {
  Run(EventActualsSource({"p(posedge clk, a)", "p(posedge clk, a)"}));
  EXPECT_EQ(FirstArgumentOp("a1"), vpiPosedgeOp);
  EXPECT_EQ(FirstArgumentOp("a2"), vpiPosedgeOp);
}

TEST_F(PropertyDeclsOfARun, TwoInstancesOfAnUntypedFormalEachReachTheirOwn) {
  Run("module top; logic clk, a, b;\n"
      "  property p(x); @(posedge clk) x; endproperty\n"
      "  a1: assert property (p(a));\n"
      "  a2: assert property (p(b));\n"
      "endmodule\n");
  const std::vector<vpiHandle> kFirst = ArgumentsOf("a1");
  const std::vector<vpiHandle> kSecond = ArgumentsOf("a2");
  ASSERT_EQ(kFirst.size(), 1U);
  ASSERT_EQ(kSecond.size(), 1U);
  EXPECT_STREQ(vpi_get_str(vpiName, kFirst[0]), "a");
  EXPECT_STREQ(vpi_get_str(vpiName, kSecond[0]), "b");
}

TEST_F(PropertyDeclsOfARun, AnEdgeKeywordEventActualIsNoArgument) {
  Run("module top; logic clk, a;\n"
      "  property p(event e, x); @(e) x; endproperty\n"
      "  a1: assert property (p(edge clk, a));\n"
      "endmodule\n");
  const std::vector<vpiHandle> kArguments = ArgumentsOf("a1");
  ASSERT_EQ(kArguments.size(), 1U);
  EXPECT_STREQ(vpi_get_str(vpiName, kArguments[0]), "a");
}

TEST_F(PropertyDeclsOfARun, AnUnclockedPropertyUnderDefaultClocking) {
  Run("module top; logic clk, a;\n"
      "  default clocking cb @(posedge clk); endclocking\n"
      "  property p(x); x; endproperty\n"
      "  a1: assert property (p(a));\n"
      "endmodule\n");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(NameReached(vpiPropertyDecl, vpi_handle(vpiProperty, a1)), "p");
}

TEST_F(PropertyDeclsOfARun, AnInstOfAWildcardImportedPropertyReachesIt) {
  Run("package pk; property p(c, x); @(posedge c) x; endproperty\n"
      "endpackage\n"
      "module top; import pk::*; logic clk, a;\n"
      "  a1: assert property (p(clk, a));\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("pk"), "p");
  ASSERT_NE(decl, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, decl), "pk::p");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_TRUE(vpi_compare_objects(
      vpi_handle(vpiPropertyDecl, vpi_handle(vpiProperty, a1)), decl));
}

TEST_F(PropertyDeclsOfARun, AnInstOfAnImportedPropertyPassesOtherImports) {
  Run("package pk; property p(c, x); @(posedge c) x; endproperty\n"
      "  property r(c); @(posedge c) 1; endproperty endpackage\n"
      "package qk; property q(c); @(posedge c) 1; endproperty endpackage\n"
      "module top; import qk::*; import pk::r; import pk::p; import qk::q;\n"
      "  logic clk, a;\n"
      "  a1: assert property (p(clk, a));\n"
      "endmodule\n");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_TRUE(vpi_compare_objects(
      vpi_handle(vpiPropertyDecl, vpi_handle(vpiProperty, a1)),
      Named(vpiPropertyDecl, By("pk"), "p")));
}

TEST(PropertyFormal, TypespecFoundPastOtherChildrenAndNullHasNoInit) {
  VpiObject attribute;
  attribute.type = vpiAttribute;
  VpiObject typespec;
  typespec.type = vpiTypespec;
  VpiObject formal;
  formal.type = vpiPropFormalDecl;
  formal.children = {&attribute, &typespec};
  EXPECT_EQ(VpiPropFormalTypespec(&formal), &typespec);
  EXPECT_EQ(VpiPropFormalInitExpr(nullptr), nullptr);
}

TEST(PropertyDeclModel, AnInstReachesItsDisableConditionAndNoOtherTag) {
  VpiObject condition;
  condition.type = vpiOperation;
  VpiObject inst;
  inst.type = vpiPropertyInst;
  inst.disable_condition = &condition;
  VpiHandle out = nullptr;
  EXPECT_TRUE(
      TryResolveProcessAndStmtRelation(vpiDisableCondition, &inst, out));
  EXPECT_EQ(out, &condition);
  out = nullptr;
  EXPECT_FALSE(TryResolveProcessAndStmtRelation(vpiTypespec, &inst, out));
  EXPECT_EQ(out, nullptr);
}
}  // namespace
}  // namespace delta
