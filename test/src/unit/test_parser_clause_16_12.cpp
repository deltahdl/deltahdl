#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §16.12: minimal named property declaration.
TEST(AssertionSemanticsParsing, PropertyDecl) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    @(posedge clk) a |-> ##1 b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "p1");
  EXPECT_TRUE(item->prop_formals.empty());
  EXPECT_EQ(item->prop_disable_iff_count, 0);
}

// §16.12 Syntax 16-16: property_port_list captures formal arguments.
TEST(AssertionSemanticsParsing, PropertyDeclWithFormals) {
  auto r = Parse(
      "module m;\n"
      "  property p2(a, b);\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "p2");
  ASSERT_EQ(item->prop_formals.size(), 2u);
  EXPECT_EQ(item->prop_formals[0], "a");
  EXPECT_EQ(item->prop_formals[1], "b");
}

// §16.12: a disable iff clause on a property_spec is captured.
TEST(AssertionSemanticsParsing, PropertyDeclDisableIffCounted) {
  auto r = Parse(
      "module m;\n"
      "  property p3;\n"
      "    @(posedge clk) disable iff (rst) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->prop_disable_iff_count, 1);
}

// §16.12: a named property may be declared in a package.
TEST(AssertionSemanticsParsing, PropertyDeclInPackage) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  property p_pkg;\n"
              "    @(posedge clk) a |-> b;\n"
              "  endproperty\n"
              "endpackage\n"));
}

// §16.12: a named property may be declared in an interface.
TEST(AssertionSemanticsParsing, PropertyDeclInInterface) {
  EXPECT_TRUE(
      ParseOk("interface i;\n"
              "  property p_if;\n"
              "    @(posedge clk) a |-> b;\n"
              "  endproperty\n"
              "endinterface\n"));
}

// §16.12: a named property may be declared in a program.
TEST(AssertionSemanticsParsing, PropertyDeclInProgram) {
  EXPECT_TRUE(
      ParseOk("program prg;\n"
              "  property p_prog;\n"
              "    @(posedge clk) a |-> b;\n"
              "  endproperty\n"
              "endprogram\n"));
}

// §16.12: a named property may be declared at compilation-unit scope.
TEST(AssertionSemanticsParsing, PropertyDeclAtCuScope) {
  EXPECT_TRUE(
      ParseOk("property p_cu;\n"
              "  @(posedge clk) a |-> b;\n"
              "endproperty\n"));
}

// §16.12: a named property may be declared in a clocking block.
TEST(AssertionSemanticsParsing, PropertyDeclInClockingBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    property p_cb;\n"
              "      a |-> b;\n"
              "    endproperty\n"
              "  endclocking\n"
              "endmodule\n"));
}

// §16.12: a named property may be declared in a generate block.
TEST(AssertionSemanticsParsing, PropertyDeclInGenerateBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  generate\n"
              "    if (1) begin : g\n"
              "      property p_gen;\n"
              "        @(posedge clk) a |-> b;\n"
              "      endproperty\n"
              "    end\n"
              "  endgenerate\n"
              "endmodule\n"));
}

// §16.12: a named property may be declared in a checker. The checker body
// routes through the same module-item parse path, so the property_declaration
// is captured among the checker's items.
TEST(AssertionSemanticsParsing, PropertyDeclInChecker) {
  auto r = Parse(
      "checker chk;\n"
      "  property p_chk;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  auto* item =
      FindItemByKind(r.cu->checkers[0]->items, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "p_chk");
}

// §16.12 Syntax 16-16: endproperty may carry a matching identifier label.
TEST(AssertionSemanticsParsing, PropertyDeclMatchingEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  property p_lbl;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty : p_lbl\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "p_lbl");
}

// §16.12 Syntax 16-16: a property_port_item may carry a default actual
// argument (`= property_actual_arg`). The formal binds to that default when an
// instance omits the argument.
TEST(AssertionSemanticsParsing, PropertyDeclWithDefaultActualArg) {
  auto r = Parse(
      "module m;\n"
      "  property p(a = 1);\n"
      "    @(posedge clk) a |-> a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formals.size(), 1u);
  EXPECT_EQ(item->prop_formals[0], "a");
}

// §16.12: beyond the positions listed in §16.8, a formal argument of a named
// property may be referenced in place of a property_expr. Here the formal `pa`
// stands as the whole body property_expr.
TEST(AssertionSemanticsParsing, PropertyFormalReferencedAsPropertyExpr) {
  auto r = Parse(
      "module m;\n"
      "  property outer(pa);\n"
      "    @(posedge clk) pa;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formals.size(), 1u);
  EXPECT_EQ(item->prop_formals[0], "pa");
}

// §16.12: the disable iff clause guards on an expression_or_dist, so the
// condition may carry a distribution (`dist`), not only a plain expression.
TEST(AssertionSemanticsParsing, PropertyDisableConditionAcceptsExprOrDist) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    disable iff (r dist {0 := 1, 1 := 1}) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->prop_disable_iff_count, 1);
}

// §16.12: a named property may be instantiated prior to its declaration.
TEST(AssertionSemanticsParsing, PropertyInstantiatedBeforeDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  assert property (p_late);\n"
      "  property p_late;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kAssertProperty), nullptr);
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kPropertyDecl), nullptr);
}

// §16.12: references to other property instances are captured for §F.4.1.
TEST(AssertionSemanticsParsing, PropertyDeclCapturesInstanceRefs) {
  auto r = Parse(
      "module m;\n"
      "  property leaf;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) leaf(a) and b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ModuleItem* root_item = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl && item->name == "root") {
      root_item = item;
      break;
    }
  }
  ASSERT_NE(root_item, nullptr);
  bool refs_leaf = false;
  for (auto ref : root_item->prop_instance_refs) {
    if (ref == "leaf") refs_leaf = true;
  }
  EXPECT_TRUE(refs_leaf);
}

}  // namespace
