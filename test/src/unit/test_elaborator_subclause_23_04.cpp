#include <gtest/gtest.h>

#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(NestedModuleElaboration, NestedModuleDoesNotAffectParent) {
  ElabFixture f;
  auto* design = Elaborate(
      "module inner; endmodule\n"
      "module m;\n"
      "  module inner_nested; endmodule\n"
      "  wire a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NestedModuleElaboration, NestedModuleWithBodyElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  module inner;\n"
      "    wire a;\n"
      "    assign a = 1;\n"
      "  endmodule\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NestedModuleElaboration, DeepNestingElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  module mid;\n"
      "    module deep;\n"
      "    endmodule\n"
      "  endmodule\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NestedModuleElaboration, MultipleNestedModulesElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  module a; endmodule\n"
      "  module b; endmodule\n"
      "  module c; endmodule\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NestedModuleElaboration, OuterScopeWireVisibleInNestedModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  module inner;\n"
      "    assign w = 1'b1;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NestedModuleElaboration, OuterParameterVisibleInNestedModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam int W = 8;\n"
      "  module inner;\n"
      "    wire [W-1:0] bus;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NestedModuleElaboration, LocalNameShadowsOuterName) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  module inner;\n"
      "    wire w;\n"
      "    assign w = 1'b0;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NestedModuleElaboration, SameNameInDifferentParents) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top;\n"
      "  module a;\n"
      "    module helper; endmodule\n"
      "  endmodule\n"
      "  module b;\n"
      "    module helper; endmodule\n"
      "  endmodule\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NestedModuleElaboration, PortlessNestedModuleImplicitlyInstantiated) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  module inner;\n"
      "    wire w;\n"
      "  endmodule\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  EXPECT_EQ(mod->children[0].module_name, "inner");
  EXPECT_EQ(mod->children[0].inst_name, "inner");
}

TEST(NestedModuleElaboration, MultiplePortlessImplicitlyInstantiated) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  module a;\n"
      "    wire w;\n"
      "  endmodule\n"
      "  module b;\n"
      "    wire w;\n"
      "  endmodule\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 2u);
}

TEST(NestedModuleElaboration,
     PortlessParameterizedNestedModuleImplicitlyInstantiated) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  module inner #(parameter int N = 4);\n"
      "    wire [N-1:0] bus;\n"
      "  endmodule\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  EXPECT_EQ(mod->children[0].module_name, "inner");
  EXPECT_EQ(mod->children[0].inst_name, "inner");
  ASSERT_NE(mod->children[0].resolved, nullptr);
  bool found_bus = false;
  for (const auto& net : mod->children[0].resolved->nets) {
    if (net.name == "bus") {
      found_bus = true;
      EXPECT_EQ(net.width, 4u);
    }
  }
  EXPECT_TRUE(found_bus);
}

TEST(NestedModuleElaboration, PortlessExplicitlyInstantiatedNotDuplicated) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  module inner;\n"
      "    wire w;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  EXPECT_EQ(mod->children[0].inst_name, "i1");
}

TEST(NestedModuleElaboration, PortedNestedModuleNotInstantiatedIsIgnored) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  module inner(input a, output b);\n"
      "    assign b = a;\n"
      "  endmodule\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(design->top_modules[0]->children.empty());
}

TEST(NestedModuleElaboration, PortedNestedModuleExplicitlyInstantiated) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire x, y;\n"
      "  module inner(input a, output b);\n"
      "    assign b = a;\n"
      "  endmodule\n"
      "  inner i1(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->children.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->children[0].module_name, "inner");
  EXPECT_EQ(design->top_modules[0]->children[0].inst_name, "i1");
}

TEST(NestedModuleElaboration, MixedPortlessAndPortedNested) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  module portless;\n"
      "    wire w;\n"
      "  endmodule\n"
      "  module ported(input a);\n"
      "  endmodule\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  EXPECT_EQ(mod->children[0].module_name, "portless");
  EXPECT_EQ(mod->children[0].inst_name, "portless");
}

TEST(NestedModuleElaboration, NestedModuleShadowsTopLevelModuleOfSameName) {
  ElabFixture f;
  auto* design = Elaborate(
      "module sub;\n"
      "  wire global_net;\n"
      "endmodule\n"
      "module m;\n"
      "  module sub;\n"
      "    wire local_net;\n"
      "  endmodule\n"
      "  sub s1();\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  ASSERT_NE(mod->children[0].resolved, nullptr);
  bool has_local = false;
  bool has_global = false;
  for (const auto& net : mod->children[0].resolved->nets) {
    if (net.name == "local_net") has_local = true;
    if (net.name == "global_net") has_global = true;
  }
  EXPECT_TRUE(has_local);
  EXPECT_FALSE(has_global);
}

TEST(NestedModuleElaboration, SameNestedNameInDifferentPartsBindsLocally) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top;\n"
      "  module part_a;\n"
      "    module and2;\n"
      "      wire net_a;\n"
      "    endmodule\n"
      "    and2 u1();\n"
      "  endmodule\n"
      "  module part_b;\n"
      "    module and2;\n"
      "      wire net_b;\n"
      "    endmodule\n"
      "    and2 u2();\n"
      "  endmodule\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  auto resolved_child = [](const RtlirModule* m,
                           std::string_view mod_name) -> const RtlirModule* {
    for (const auto& c : m->children)
      if (c.module_name == mod_name) return c.resolved;
    return nullptr;
  };
  auto has_net = [](const RtlirModule* m, std::string_view n) {
    for (const auto& net : m->nets)
      if (net.name == n) return true;
    return false;
  };

  const RtlirModule* part_a = resolved_child(design->top_modules[0], "part_a");
  const RtlirModule* part_b = resolved_child(design->top_modules[0], "part_b");
  ASSERT_NE(part_a, nullptr);
  ASSERT_NE(part_b, nullptr);

  const RtlirModule* a_and2 = resolved_child(part_a, "and2");
  const RtlirModule* b_and2 = resolved_child(part_b, "and2");
  ASSERT_NE(a_and2, nullptr);
  ASSERT_NE(b_and2, nullptr);

  EXPECT_TRUE(has_net(a_and2, "net_a"));
  EXPECT_FALSE(has_net(a_and2, "net_b"));
  EXPECT_TRUE(has_net(b_and2, "net_b"));
  EXPECT_FALSE(has_net(b_and2, "net_a"));
}

TEST(NestedModuleElaboration, ImplicitInstanceElaboratesNestedBody) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  module inner;\n"
      "    wire inner_net;\n"
      "  endmodule\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  ASSERT_NE(mod->children[0].resolved, nullptr);
  bool has_inner_net = false;
  for (const auto& net : mod->children[0].resolved->nets) {
    if (net.name == "inner_net") has_inner_net = true;
  }
  EXPECT_TRUE(has_inner_net);
}

const RtlirNet* NestedModuleNet(const RtlirDesign* design,
                                std::string_view name) {
  const auto& children = design->top_modules[0]->children;
  if (children.empty() || children[0].resolved == nullptr) return nullptr;
  for (const auto& net : children[0].resolved->nets) {
    if (net.name == name) return &net;
  }
  return nullptr;
}

TEST(NestedModuleElaboration, UndeclaredImplicitNetOfNestedModuleIsItsOwn) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top;\n"
      "  wire x;\n"
      "  module M(output o);\n"
      "    assign q = 1'b1;\n"
      "    assign o = q;\n"
      "  endmodule\n"
      "  M m1(.o(x));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* q = NestedModuleNet(design, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_FALSE(q->refers_outward);
}

TEST(NestedModuleElaboration, ImplicitNetForAnOuterNameRefersOutward) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top;\n"
      "  wire w;\n"
      "  module M;\n"
      "    assign w = 1'b1;\n"
      "  endmodule\n"
      "  M m();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* w = NestedModuleNet(design, "w");
  ASSERT_NE(w, nullptr);
  EXPECT_TRUE(w->refers_outward);
}

TEST(NestedModuleElaboration,
     ImplicitNetForAnOuterNameDeclaredBelowTheNestedDeclarationIsItsOwn) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top;\n"
      "  module M;\n"
      "    assign w = 1'b1;\n"
      "  endmodule\n"
      "  wire w;\n"
      "  M m();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* w = NestedModuleNet(design, "w");
  ASSERT_NE(w, nullptr);
  EXPECT_FALSE(w->refers_outward);
}

TEST(NestedModuleElaboration,
     ImplicitlyInstantiatedNestedModuleOwnsANetDeclaredBelowIt) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top;\n"
      "  module M;\n"
      "    assign w = 1'b1;\n"
      "  endmodule\n"
      "  wire w;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* w = NestedModuleNet(design, "w");
  ASSERT_NE(w, nullptr);
  EXPECT_FALSE(w->refers_outward);
}

TEST(NestedModuleElaboration,
     OuterNetDeclaredBetweenAnInstanceAboveAndTheNestedDeclarationIsOuter) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top;\n"
      "  M m();\n"
      "  wire w;\n"
      "  module M;\n"
      "    assign w = 1'b1;\n"
      "  endmodule\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* w = NestedModuleNet(design, "w");
  ASSERT_NE(w, nullptr);
  EXPECT_TRUE(w->refers_outward);
}

TEST(NestedModuleElaboration,
     InstanceAboveTheNestedDeclarationOwnsANetDeclaredBelowTheDeclaration) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top;\n"
      "  M m();\n"
      "  module M;\n"
      "    assign w = 1'b1;\n"
      "  endmodule\n"
      "  wire w;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* w = NestedModuleNet(design, "w");
  ASSERT_NE(w, nullptr);
  EXPECT_FALSE(w->refers_outward);
}

const RtlirNet* DoublyNestedModuleNet(const RtlirDesign* design,
                                      std::string_view name) {
  const auto& children = design->top_modules[0]->children;
  if (children.empty() || children[0].resolved == nullptr) return nullptr;
  const auto& inner = children[0].resolved->children;
  if (inner.empty() || inner[0].resolved == nullptr) return nullptr;
  for (const auto& net : inner[0].resolved->nets) {
    if (net.name == name) return &net;
  }
  return nullptr;
}

TEST(NestedModuleElaboration, DoublyNestedImplicitNetRefersOutwardByOrder) {
  ElabFixture above;
  auto* design_above = Elaborate(
      "module top;\n"
      "  wire v;\n"
      "  module A;\n"
      "    module B;\n"
      "      assign v = 1'b1;\n"
      "    endmodule\n"
      "    B b();\n"
      "  endmodule\n"
      "  A a();\n"
      "endmodule\n",
      above, "top");
  ASSERT_NE(design_above, nullptr);
  EXPECT_FALSE(above.has_errors);
  const auto* v_above = DoublyNestedModuleNet(design_above, "v");
  ASSERT_NE(v_above, nullptr);
  EXPECT_TRUE(v_above->refers_outward);

  ElabFixture below;
  auto* design_below = Elaborate(
      "module top;\n"
      "  module A;\n"
      "    module B;\n"
      "      assign v = 1'b1;\n"
      "    endmodule\n"
      "    B b();\n"
      "  endmodule\n"
      "  A a();\n"
      "  wire v;\n"
      "endmodule\n",
      below, "top");
  ASSERT_NE(design_below, nullptr);
  EXPECT_FALSE(below.has_errors);
  const auto* v_below = DoublyNestedModuleNet(design_below, "v");
  ASSERT_NE(v_below, nullptr);
  EXPECT_FALSE(v_below->refers_outward);
}

const RtlirModule* ChildModule(const RtlirModule* m, std::string_view inst) {
  for (const auto& c : m->children) {
    if (c.inst_name == inst) return c.resolved;
  }
  return nullptr;
}

bool DeclaresNet(const RtlirModule* m, std::string_view name) {
  for (const auto& net : m->nets) {
    if (net.name == name) return true;
  }
  return false;
}

TEST(NestedModuleElaboration, AnEnclosingModulesNestedDeclarationsAreVisible) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top;\n"
      "  interface bus; endinterface\n"
      "  module sib(input logic a); wire outer_sib; endmodule\n"
      "  module leaf(input logic a); wire outer_leaf; endmodule\n"
      "  module inner;\n"
      "    module leaf(input logic a); wire inner_leaf; endmodule\n"
      "    module deep; virtual bus dv; endmodule\n"
      "    virtual bus vb; logic x;\n"
      "    sib s(.a(x)); leaf l(.a(x)); deep d();\n"
      "  endmodule\n"
      "  inner i();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirModule* inner = ChildModule(design->top_modules[0], "i");
  ASSERT_NE(inner, nullptr);
  const RtlirModule* sib = ChildModule(inner, "s");
  ASSERT_NE(sib, nullptr);
  EXPECT_TRUE(DeclaresNet(sib, "outer_sib"));
  const RtlirModule* leaf = ChildModule(inner, "l");
  ASSERT_NE(leaf, nullptr);
  EXPECT_TRUE(DeclaresNet(leaf, "inner_leaf"));
  EXPECT_FALSE(DeclaresNet(leaf, "outer_leaf"));
}

TEST(NestedModuleElaboration, ATopLevelModuleSeesNoEnclosingNestedDeclaration) {
  ElabFixture f;
  Elaborate(
      "module ext; virtual bus vb; endmodule\n"
      "module top;\n"
      "  interface bus; endinterface\n"
      "  module inner; ext e(); endmodule\n"
      "  inner i();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unknown interface 'bus' in virtual interface declaration", 1, "25.9"));
}

}  // namespace
