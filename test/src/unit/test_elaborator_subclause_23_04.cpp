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

}  // namespace
