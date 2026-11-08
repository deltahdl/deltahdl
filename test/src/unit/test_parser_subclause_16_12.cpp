#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

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

TEST(AssertionSemanticsParsing, PropertyDeclInPackage) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  property p_pkg;\n"
              "    @(posedge clk) a |-> b;\n"
              "  endproperty\n"
              "endpackage\n"));
}

TEST(AssertionSemanticsParsing, PropertyDeclInInterface) {
  EXPECT_TRUE(
      ParseOk("interface i;\n"
              "  property p_if;\n"
              "    @(posedge clk) a |-> b;\n"
              "  endproperty\n"
              "endinterface\n"));
}

TEST(AssertionSemanticsParsing, PropertyDeclInProgram) {
  EXPECT_TRUE(
      ParseOk("program prg;\n"
              "  property p_prog;\n"
              "    @(posedge clk) a |-> b;\n"
              "  endproperty\n"
              "endprogram\n"));
}

TEST(AssertionSemanticsParsing, PropertyDeclAtCuScope) {
  EXPECT_TRUE(
      ParseOk("property p_cu;\n"
              "  @(posedge clk) a |-> b;\n"
              "endproperty\n"));
}

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

TEST(PropertyDeclaration, MalformedPropertyHeaderNames16_12) {
  auto r = Parse(
      "module m;\n"
      "  property p\n"
      "    a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';'", 3, "16.12"));
}

TEST(AssertionSemanticsParsing, APropertyFormalsDefaultActualIsRecorded) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b;\n"
      "  property p(x, y = b, int d = 3, untyped e = $inferred_clock,\n"
      "            property q = a |-> b);\n"
      "    x ##d y;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  std::string recorded;
  for (const Expr* def : item->prop_formal_defaults) {
    if (def == nullptr) {
      recorded += '-';
    } else if (def->property_actual != nullptr) {
      recorded += 'P';
    } else if (def->kind == ExprKind::kIdentifier) {
      recorded += def->text == "b" ? 'I' : '?';
    } else {
      recorded += def->kind == ExprKind::kIntegerLiteral ? 'L' : '?';
    }
  }
  std::string marked;
  for (bool has : item->prop_formal_has_default) marked += has ? '1' : '0';
  EXPECT_EQ(recorded, "-IL-P");
  EXPECT_EQ(marked, "01111");
}

TEST(AssertionSemanticsParsing, ASpecWithoutItsSemicolonIsReadAsATree) {
  auto r = Parse(
      "module m;\n"
      "  property p_delay;\n"
      "    @(posedge clk) a\n"
      "  endproperty\n"
      "  assert property (@(posedge clk) a ##1 b);\n"
      "  property p_repetition;\n"
      "    @(posedge clk) a\n"
      "  endproperty\n"
      "  assert property (@(posedge clk) a [*2]);\n"
      "  property p_throughout;\n"
      "    @(posedge clk) a\n"
      "  endproperty\n"
      "  assert property (@(posedge clk) a throughout b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (std::string_view name : {"p_delay", "p_repetition", "p_throughout"}) {
    SCOPED_TRACE(name);
    const ModuleItem* decl = FindItemByName(r.cu->modules[0]->items, name);
    ASSERT_NE(decl, nullptr);
    ASSERT_EQ(decl->prop_clock.size(), 1u);
    EXPECT_EQ(decl->prop_clock[0].edge, Edge::kPosedge);
    ASSERT_NE(decl->prop_body_tree, nullptr);
    EXPECT_EQ(decl->prop_body_tree->kind, PropertyExprNode::Kind::kBoolean);
    ASSERT_NE(decl->prop_body_tree->boolean, nullptr);
    EXPECT_EQ(decl->prop_body_tree->boolean->text, "a");
  }
}

TEST(AssertionSemanticsParsing, AClockedBooleanSpecWithoutItsSemicolonIsKept) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    @(posedge clk) disable iff (rst) !req || en\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* decl = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(decl, nullptr);
  ASSERT_EQ(decl->prop_clock.size(), 1u);
  EXPECT_NE(decl->prop_disable_iff, nullptr);
  ASSERT_NE(decl->prop_body_expr, nullptr);
  EXPECT_EQ(decl->prop_body_expr->kind, ExprKind::kBinary);
}

}  // namespace
