#include <gtest/gtest.h>

#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;
namespace {

const RtlirModule* InstanceNamed(const RtlirModule* parent,
                                 std::string_view name) {
  for (const auto& child : parent->children) {
    if (child.inst_name == name) return child.resolved;
  }
  return nullptr;
}

TEST(InterfaceDefinitions, EmptyInterfaceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc("interface ifc; endinterface\n", f, "ifc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterfaceInstantiationGrammar, ElaborationInterfaceInstInModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface my_bus(input logic clk, input logic rst);\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk, rst;\n"
      "  my_bus bus0(.clk(clk), .rst(rst));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "my_bus");
  EXPECT_EQ(top->children[0].inst_name, "bus0");
  EXPECT_NE(top->children[0].resolved, nullptr);
}

TEST(InterfaceInstantiationGrammar, ElaborationInterfaceInsideInterface) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface inner_if(input logic sig);\n"
      "endinterface\n"
      "interface outer_if;\n"
      "  logic sig;\n"
      "  inner_if u0(.sig(sig));\n"
      "endinterface\n"
      "module top;\n"
      "  outer_if oi();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "outer_if");
  auto* outer = top->children[0].resolved;
  ASSERT_NE(outer, nullptr);
  ASSERT_GE(outer->children.size(), 1u);
  EXPECT_EQ(outer->children[0].module_name, "inner_if");
  EXPECT_NE(outer->children[0].resolved, nullptr);
}

TEST(InterfaceInstantiationGrammar, ElaborationInterfaceInstPortBindings) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface simple_if(input logic data);\n"
      "endinterface\n"
      "module top;\n"
      "  logic d;\n"
      "  simple_if u0(.data(d));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_GE(top->children[0].port_bindings.size(), 1u);
  EXPECT_EQ(top->children[0].port_bindings[0].port_name, "data");
}

TEST(InterfaceInstantiationGrammar, ElaborationMultipleInstances) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface my_if(input logic clk);\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk;\n"
      "  my_if u0(.clk(clk)), u1(.clk(clk));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 2u);
  EXPECT_EQ(top->children[0].module_name, "my_if");
  EXPECT_EQ(top->children[0].inst_name, "u0");
  EXPECT_NE(top->children[0].resolved, nullptr);
  EXPECT_EQ(top->children[1].module_name, "my_if");
  EXPECT_EQ(top->children[1].inst_name, "u1");
  EXPECT_NE(top->children[1].resolved, nullptr);
}

TEST(InterfaceInstantiationGrammar, ParameterOverrideAndInstanceArray) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface myinterface #(parameter int P = 8);\n"
      "  logic [P-1:0] data;\n"
      "endinterface\n"
      "module top;\n"
      "  myinterface #(100) scalar1(), vector[9:0]();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 11u);
  for (const auto& child : top->children) {
    EXPECT_EQ(child.module_name, "myinterface");
    ASSERT_NE(child.resolved, nullptr);
    EXPECT_TRUE(child.resolved->is_interface);
    const RtlirParamDecl* p = nullptr;
    for (const auto& pd : child.resolved->params)
      if (pd.name == "P") p = &pd;
    ASSERT_NE(p, nullptr);
    EXPECT_TRUE(p->is_resolved);
    EXPECT_EQ(p->resolved_value, 100);
  }
}

TEST(InterfaceInstantiationGrammar, ElaborationUnresolvedInterface) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top;\n"
      "  nonexistent_if u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].resolved, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unknown module 'nonexistent_if'", 2, "23.3.2"));
}

TEST(InterfaceDefinitions, ModuleDeclInsideInterfaceIsError) {
  ElabFixture f;
  Elaborate(
      "interface ifc;\n"
      "  module bad;\n"
      "  endmodule\n"
      "endinterface\n"
      "module top;\n"
      "  ifc u0();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'bad' cannot be declared inside interface "
                            "'ifc'",
                            2, "25.3"));
}

TEST(InterfaceDefinitions, ModuleInstantiationInsideInterfaceIsError) {
  ElabFixture f;
  Elaborate(
      "module sub;\n"
      "endmodule\n"
      "interface ifc;\n"
      "  sub u0();\n"
      "endinterface\n"
      "module top;\n"
      "  ifc u1();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'sub' cannot be instantiated inside "
                            "interface 'ifc'",
                            4, "25.3"));
}

TEST(InterfaceDefinitions, NotImplicitlyInstantiated) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface inner;\n"
      "endinterface\n"
      "module top;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_TRUE(design->top_modules[0]->children.empty());
}

TEST(InterfaceDefinitions, NestedInterfaceNotImplicitlyInstantiated) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface outer;\n"
      "  interface inner;\n"
      "  endinterface\n"
      "endinterface\n"
      "module top;\n"
      "  outer o0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  auto* outer = top->children[0].resolved;
  ASSERT_NE(outer, nullptr);
  EXPECT_TRUE(outer->children.empty());
}

TEST(InterfaceDefinitions, InterfaceExcludedFromAutoTopModules) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "interface lone_if;\n"
      "  logic x;\n"
      "endinterface\n"
      "module top;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
}

TEST(InterfacePortActual, InterfaceInstanceActualElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface ib;\n"
      "  logic x;\n"
      "endinterface\n"
      "module sub(ib p);\n"
      "endmodule\n"
      "module top;\n"
      "  ib bus();\n"
      "  sub s(.p(bus));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_GE(design->top_modules[0]->children.size(), 2u);
}

TEST(InterfacePortActual, NonInterfaceActualIsError) {
  ElabFixture f;
  Elaborate(
      "interface ib;\n"
      "  logic x;\n"
      "endinterface\n"
      "module sub(ib p);\n"
      "endmodule\n"
      "module top;\n"
      "  logic not_an_iface;\n"
      "  sub s(.p(not_an_iface));\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interface port 'p' must be connected to an "
                            "interface instance or interface port",
                            8, "23.3.3.4"));
}

TEST(InterfacePortHierRef, InstanceInAnotherModuleIsConnected) {
  EXPECT_TRUE(
      ElabOk("interface ifc; logic a; endinterface\n"
             "module holder; ifc i(); endmodule\n"
             "module user(ifc p); endmodule\n"
             "module top; holder h(); user u(h.i); endmodule\n"));
}

TEST(InterfacePortHierRef, ModportAndDeeperPathsAreConnected) {
  EXPECT_TRUE(
      ElabOk("interface ifc; logic a; modport mp(input a); endinterface\n"
             "module holder; ifc i(); endmodule\n"
             "module outer; holder h(); endmodule\n"
             "module user(ifc p); endmodule\n"
             "module top; holder h(); outer o();\n"
             "  user u1(h.i.mp); user u2(o.h.i);\n"
             "endmodule\n"));
}

TEST(InterfacePortHierRef, PathFromTheModulesOwnNameIsConnected) {
  EXPECT_TRUE(
      ElabOk("interface ifc; logic a; modport mp(input a); endinterface\n"
             "module user(ifc p); endmodule\n"
             "module top; ifc i(); user u1(top.i); user u2(top.i.mp);\n"
             "endmodule\n"));
}

TEST(InterfacePortHierRef, FullPathFromATopModuleIsConnected) {
  EXPECT_TRUE(
      ElabOk("interface ifc; logic a; modport mp(input a); endinterface\n"
             "module user(ifc p); endmodule\n"
             "module holder; ifc i(); endmodule\n"
             "module mid; user u1(top.i); user u2(top.i.mp);\n"
             "  user u3(top.h.i); endmodule\n"
             "module top; ifc i(); holder h(); mid m(); endmodule\n"));
}

TEST(InterfacePortHierRef, PathNotEndingAtAnInstanceIsRefused) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; logic a; modport mp(input a); endinterface\n"
      "module leaf; endmodule\n"
      "module holder; ifc i(); ifc ia[2](); leaf k(); endmodule\n"
      "module user(ifc p); endmodule\n"
      "module top; holder h();\n"
      "  user u1(h.k);\n"
      "  user u2(h.ia);\n"
      "  user u3(h.i.mp.a);\n"
      "endmodule\n",
      f, "top");
  for (int line : {6, 7, 8}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "interface port 'p' must be connected to an "
                              "interface instance or interface port",
                              line, "23.3.3.4"));
  }
}

TEST(InterfacePortHierRef, PathThroughArrayedInstanceIsRefused) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; logic a; endinterface\n"
      "module holder; ifc i(); endmodule\n"
      "module user(ifc p); endmodule\n"
      "module top; holder h[2]();\n"
      "  user u1(h[0].i);\n"
      "  user u2(h.i);\n"
      "endmodule\n",
      f, "top");
  for (int line : {5, 6}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "the actual of interface port 'p' resolves "
                              "through the arrayed instance 'h'",
                              line, "25.3"));
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "interface port 'p' must be connected to an "
                               "interface instance or interface port",
                               line, "23.3.3.4"));
  }
}

TEST(InterfacePortHierRef, PathThroughGenerateBlockIsRefused) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; logic a; endinterface\n"
      "module user(ifc p); endmodule\n"
      "module top;\n"
      "  if (1) begin : g ifc i(); end\n"
      "  for (genvar k = 0; k < 2; k++) begin : l ifc i(); end\n"
      "  user u1(g.i);\n"
      "  user u2(l[1].i);\n"
      "endmodule\n",
      f, "top");
  for (int line : {6, 7}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "the actual of interface port 'p' resolves "
                              "through a generate block",
                              line, "25.3"));
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "interface port 'p' must be connected to an "
                               "interface instance or interface port",
                               line, "23.3.3.4"));
  }
}

TEST(ArrayedInterfaceDefparam, OutsideTheInstanceIsRefused) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc; logic a; endinterface\n"
      "module other; parameter P = 1; endmodule\n"
      "module user(ifc p[2]);\n"
      "  defparam top.o.P = 5;\n"
      "endmodule\n"
      "module single(ifc p);\n"
      "  defparam top.o.P = 6;\n"
      "endmodule\n"
      "module top; ifc ia[2](); other o(); user u(ia); single v(ia[0]);\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  for (int line : {4, 7}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "defparam inside an instance whose port actuals "
                              "refer to an arrayed interface reaches a "
                              "parameter outside that instance",
                              line, "25.3"));
  }
  const RtlirModule* o = InstanceNamed(design->top_modules[0], "o");
  ASSERT_NE(o, nullptr);
  EXPECT_EQ(o->params[0].resolved_value, 1);
}

TEST(ArrayedInterfaceDefparam, WithinTheInstanceIsApplied) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc; logic a; endinterface\n"
      "module leaf; parameter Q = 1; endmodule\n"
      "module user(ifc p[2]);\n"
      "  leaf s();\n"
      "  defparam top.u.s.Q = 7;\n"
      "endmodule\n"
      "module top; ifc ia[2](); user u(ia); endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirModule* u = InstanceNamed(design->top_modules[0], "u");
  ASSERT_NE(u, nullptr);
  const RtlirModule* s = InstanceNamed(u, "s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->params[0].resolved_value, 7);
}

TEST(InterfaceDefinitions, ExternInterfacePrototypeIsNoDefinition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern interface ifc(input logic clk);\n"
      "interface ifc(.*);\n"
      "  logic data;\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk;\n"
      "  ifc i(clk);\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->children.size(), 1u);
  auto* ifc = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(ifc, nullptr);
  ASSERT_EQ(ifc->ports.size(), 1u);
  EXPECT_EQ(ifc->ports[0].name, "clk");
  ASSERT_FALSE(ifc->variables.empty());
  EXPECT_EQ(ifc->variables[0].name, "data");
}

}  // namespace
