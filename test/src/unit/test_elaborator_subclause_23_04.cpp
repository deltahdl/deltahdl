#include <gtest/gtest.h>

#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

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

// §23.4: the implicit-instantiation rule triggers on a nested module having no
// PORTS. A parameter is not a port, so a port-less nested module that merely
// carries a defaulted parameter is still implicitly instantiated once with an
// instance name equal to the module name. The default is applied when the
// implicit instance is elaborated, sizing the nested net -- proving the
// instance is a real elaboration and that parameter ports do not count as ports
// for this rule.
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

// §23.4: a name declared in a local (nested) module hides an outer name of the
// same kind. A nested module declaration therefore shadows a top-level module
// sharing its name, so the same identifier can denote different modules in
// different parts of the design. Here the instance of `sub` inside `m` must
// bind to the nested `sub` (whose net is local_net), not the top-level `sub`.
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

// §23.4: nested module declarations can build a library of modules local to
// part of a design, letting the same module name appear in different parts and
// denote different modules (the standard's `and2`-in-different-parts example).
// Two sibling parts each declare a nested `and2` with a distinguishing net and
// each instantiates it; every instance must bind to the `and2` local to its own
// part, proving each enclosing scope keeps its own nested-module table.
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

  // Each part's `and2` carries only its own local net -- the two same-named
  // nested modules are distinct definitions, not one shared module.
  EXPECT_TRUE(has_net(a_and2, "net_a"));
  EXPECT_FALSE(has_net(a_and2, "net_b"));
  EXPECT_TRUE(has_net(b_and2, "net_b"));
  EXPECT_FALSE(has_net(b_and2, "net_a"));
}

// §23.4: the implicit instantiation of a port-less nested module is a real
// instantiation -- the nested module's body is elaborated, not merely
// registered. The resolved instance must carry the nested module's contents.
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

// The net named `name` among the nested module's, which is the first child of
// the design's top module, or null when it holds none of the name.
const RtlirNet* NestedModuleNet(const RtlirDesign* design,
                                std::string_view name) {
  const auto& children = design->top_modules[0]->children;
  if (children.empty() || children[0].resolved == nullptr) return nullptr;
  for (const auto& net : children[0].resolved->nets) {
    if (net.name == name) return &net;
  }
  return nullptr;
}

// §6.10 with §23.4: a name a continuous assignment inside a nested module
// writes that no module declares, the enclosing ones included, is an implicit
// net of the nested module's own scope, so the net the elaborator makes for
// it refers to nothing outward. The lowerer reads RtlirNet::refers_outward to
// materialize such a net under each instance.
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

// §23.4: a continuous assignment inside a nested module to a name the
// enclosing module declares reaches that outer net, and the net the elaborator
// pushes onto the nested module's list for the reference stands for it, so it
// is marked as referring outward and no instance materializes it.
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

// §6.10 with §23.4: the outer name space being visible does not make a name
// declared below the nested module's text one the nested module's assignment
// was preceded by, and §6.10 assumes an implicit net of the assignment's own
// scope for a name "not declared previously" there or in a scope it can
// directly reference. An outer w declared between M's endmodule and its
// instance is declared after the assignment, so M's net w refers to nothing
// outward. The names visible to M were taken where the instance stood, so w
// was among them and the net was marked outward.
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

// The same rule for an instance §23.4 implies at the end of the module: the
// names visible to M were taken there, after every item, so an outer w
// declared anywhere below M counted as declared previously and the net was
// marked outward. It is M's own.
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

// §6.10 measures "previously" from the assignment's text, which stands in M's
// declaration, wherever M's instance is written. With the instance above the
// declaration and the outer w between the two, w is declared above M's text,
// so M's assignment writes the outer net and M's net for it refers outward.
// The names visible to M were taken where the instance stood, above w, so w
// was not among them and M took the net as its own.
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

// The same instance above its declaration with the outer w declared below
// the declaration: w is declared after M's assignment at every point, so M's
// net is its own, as it is when the instance is written below.
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

// The net named `name` among the nets of the nested module two levels down:
// the first child of the top module's first child, or null.
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

// §23.4 through two levels: B is declared and instantiated in A, itself
// declared and instantiated in top, so top's names are visible in B by way of
// A's chain of enclosing scopes, and a v declared above A is what B's
// assignment writes -- its net refers outward. Declared below A, v is not
// declared previously at either level, and B's net is its own.
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

}  // namespace
