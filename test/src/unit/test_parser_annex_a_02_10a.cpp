#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- assert_property_statement ---

TEST(AssertionDeclParsing, ConcurrentAssertionItem_AssertProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->loc.IsValid());
}

TEST(AssertionDeclParsing, AssertProperty_WithActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b)\n"
      "    $display(\"pass\"); else $display(\"fail\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_pass_stmt, nullptr);
  EXPECT_NE(item->assert_fail_stmt, nullptr);
}

TEST(AssertionDeclParsing, AssertProperty_PassOnly) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a) $display(\"ok\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_pass_stmt, nullptr);
  EXPECT_EQ(item->assert_fail_stmt, nullptr);
}

TEST(AssertionDeclParsing, AssertProperty_FailOnly) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a |-> b) else $error(\"fail\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->assert_pass_stmt, nullptr);
  EXPECT_NE(item->assert_fail_stmt, nullptr);
}

TEST(AssertionParsing, AssertPropertySimple) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a && b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

TEST(AssertionParsing, AssertPropertyModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAssertProperty) {
      found = true;
      EXPECT_NE(item->assert_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(AssertionParsing, AssertPropertyWithElse) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ack)\n"
      "    $display(\"ok\"); else $error(\"fail\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_pass_stmt, nullptr);
  EXPECT_NE(ap->assert_fail_stmt, nullptr);
}

TEST(AssertionParsing, AssertPropertyClockedPosedge) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

TEST(AssertionParsing, AssertPropertyPassAndFailActions) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ack)\n"
      "    $display(\"pass\"); else $error(\"fail\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_pass_stmt, nullptr);
  EXPECT_NE(ap->assert_fail_stmt, nullptr);
}

TEST(AssertionParsing, AssertPropertyPassOnly) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) valid)\n"
      "    $display(\"passed\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_pass_stmt, nullptr);
  EXPECT_EQ(ap->assert_fail_stmt, nullptr);
}

TEST(AssertionParsing, AssertPropertyFailOnly) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b)\n"
      "    else $error(\"failed\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_EQ(ap->assert_pass_stmt, nullptr);
  EXPECT_NE(ap->assert_fail_stmt, nullptr);
}

TEST(AssertionParsing, ConcurrentAssertWithClock) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

TEST(AssertionParsing, ConcurrentAssertNegedgeClock) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(negedge clk) a |-> b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ConcurrentAssertionParsing, AssertPropertyStatement) {
  auto r = Parse(R"(
    module m;
      logic clk, a, b;
      assert property (@(posedge clk) a |-> b);
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);

  bool found_assert = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAssertProperty) {
      found_assert = true;
    }
  }
  EXPECT_TRUE(found_assert);
}

TEST(AssertionStatementSyntaxParsing, AssertPropertyModule) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a |-> b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
}

TEST(AssertionStatementSyntaxParsing, AssertPropertyActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a) $display(\"pass\"); else $display(\"fail\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->assert_pass_stmt, nullptr);
  ASSERT_NE(item->assert_fail_stmt, nullptr);
}

// --- assume_property_statement ---

TEST(AssertionDeclParsing, AssumeProperty_WithElseAction) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req)\n"
      "    $display(\"ok\"); else $error(\"bad\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_pass_stmt, nullptr);
  EXPECT_NE(item->assert_fail_stmt, nullptr);
}

TEST(AssertionDeclParsing, AssumeProperty_NoActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req |-> ack);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->assert_pass_stmt, nullptr);
  EXPECT_EQ(item->assert_fail_stmt, nullptr);
}

TEST(AssertionParsing, AssumePropertyModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) valid);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAssumeProperty) {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(AssertionParsing, AssumePropertySimple) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) valid);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

TEST(AssertionParsing, AssumePropertyClocked) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req |-> gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

TEST(AssertionParsing, AssumePropertyElseAction) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) en |-> ready)\n"
      "    else $error(\"assumption violated\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_EQ(ap->assert_pass_stmt, nullptr);
  EXPECT_NE(ap->assert_fail_stmt, nullptr);
}

TEST(AssertionParsing, ConcurrentAssumePropertyWithAction) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req |-> gnt)\n"
      "    else $error(\"assumption failed\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_fail_stmt, nullptr);
}

TEST(ConcurrentAssertionParsing, AssumePropertyStatement) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk, req, gnt;
      assume property (@(posedge clk) req |-> ##[1:3] gnt);
    endmodule
  )"));
}

TEST(AssertionStatementSyntaxParsing, AssumePropertyModule) {
  auto r = Parse(
      "module m;\n"
      "  assume property (req |-> ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(item, nullptr);
}

// --- cover_property_statement / cover_sequence_statement ---

TEST(AssertionDeclParsing, ConcurrentAssertionItem_CoverProperty) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(item, nullptr);
}

TEST(AssertionDeclParsing, CoverSequence_Basic) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverSequence);
  ASSERT_NE(item, nullptr);
}

TEST(AssertionDeclParsing, CoverSequence_WithPassAction) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (@(posedge clk) a ##2 b ##1 c)\n"
      "    $display(\"seq covered\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverSequence);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_pass_stmt, nullptr);
}

TEST(AssertionDeclParsing, CoverSequence_WithDisableIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  cover sequence (@(posedge clk) disable iff (rst) a ##1 b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, CoverSequence_Kind) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverSequence);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kCoverSequence);
}

TEST(AssertionDeclParsing, CoverProperty_WithPassStmt) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b)\n"
      "    $display(\"covered\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_pass_stmt, nullptr);
}

TEST(AssertionDeclParsing, CoverSequence_HasAssertExpr) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverSequence);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_expr, nullptr);
}

TEST(AssertionParsing, CoverPropertyModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a && b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kCoverProperty) {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(AssertionParsing, CoverPropertySimple) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a && b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* cp =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(cp, nullptr);
  EXPECT_NE(cp->assert_expr, nullptr);
}

TEST(AssertionParsing, CoverPropertyClocked) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* cp =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(cp, nullptr);
  EXPECT_NE(cp->assert_expr, nullptr);
}

TEST(AssertionParsing, CoverPropertyPassAction) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b)\n"
      "    $display(\"covered\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* cp =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(cp, nullptr);
  EXPECT_NE(cp->assert_pass_stmt, nullptr);
}

TEST(AssertionParsing, CoverSequenceWithPassAction) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##2 b ##1 c)\n"
      "    $display(\"seq covered\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* cp =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(cp, nullptr);
  EXPECT_NE(cp->assert_pass_stmt, nullptr);
}

TEST(AssertionParsing, ConcurrentCoverPropertyWithStmt) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b)\n"
      "    $display(\"covered\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* cp =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(cp, nullptr);
}

TEST(ConcurrentAssertionParsing, CoverPropertyStatement) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk, a, b;
      cover property (@(posedge clk) a ##1 b);
    endmodule
  )"));
}

TEST(AssertionStatementSyntaxParsing, CoverPropertyModule) {
  auto r = Parse(
      "module m;\n"
      "  cover property (a && b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kCoverProperty);
  ASSERT_NE(item, nullptr);
}

TEST(AssertionStatementSyntaxParsing, CoverSequenceModule) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (a ##1 b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kCoverSequence);
  ASSERT_NE(item, nullptr);
}

TEST(AssertionStatementSyntaxParsing, CoverPropertyPassAction) {
  auto r = Parse(
      "module m;\n"
      "  cover property (a) $display(\"covered\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kCoverProperty);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->assert_pass_stmt, nullptr);
}

// --- restrict_property_statement ---

TEST(AssertionDeclParsing, RestrictProperty_Basic) {
  auto r = Parse(
      "module m;\n"
      "  restrict property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r.cu->modules[0]->items,
                              ModuleItemKind::kRestrictProperty);
  ASSERT_NE(item, nullptr);
}

TEST(AssertionDeclParsing, RestrictProperty_Kind) {
  auto r = Parse(
      "module m;\n"
      "  restrict property (@(posedge clk) req |-> ##[1:3] ack);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r.cu->modules[0]->items,
                              ModuleItemKind::kRestrictProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kRestrictProperty);
  EXPECT_TRUE(item->loc.IsValid());
}

TEST(AssertionDeclParsing, RestrictProperty_WithDisableIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  restrict property (\n"
              "    @(posedge clk) disable iff (rst) a |-> b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, RestrictProperty_HasAssertExpr) {
  auto r = Parse(
      "module m;\n"
      "  restrict property (@(posedge clk) a);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r.cu->modules[0]->items,
                              ModuleItemKind::kRestrictProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_expr, nullptr);
}

TEST(AssertionStatementSyntaxParsing, RestrictPropertyModule) {
  auto r = Parse(
      "module m;\n"
      "  restrict property (clk);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kRestrictProperty);
  ASSERT_NE(item, nullptr);
}

// --- concurrent_assertion_statement (mixed) ---

TEST(AssertionDeclParsing, ConcurrentAssertionItem_AssumeProperty) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req |-> ack);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(item, nullptr);
}

TEST(AssertionDeclParsing, AllFiveConcurrentAssertionTypes) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a |-> b);\n"
      "  assume property (c |-> d);\n"
      "  cover property (e ##1 f);\n"
      "  cover sequence (g ##1 h);\n"
      "  restrict property (i |-> j);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty),
      nullptr);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty),
      nullptr);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty),
      nullptr);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverSequence),
      nullptr);
  ASSERT_NE(FindItemByKind(r.cu->modules[0]->items,
                           ModuleItemKind::kRestrictProperty),
            nullptr);
}

TEST(AssertionParsing, PropertyDeclAndAssertProperty) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "  assert property (p1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found_prop = false;
  bool found_assert = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl) found_prop = true;
    if (item->kind == ModuleItemKind::kAssertProperty) found_assert = true;
  }
  EXPECT_TRUE(found_prop);
  EXPECT_TRUE(found_assert);
}

TEST(AssertionParsing, MultipleConcurrentAssertions) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "  assume property (@(posedge clk) en);\n"
      "  cover property (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(CountItemsByKind(r.cu->modules[0]->items,
                             ModuleItemKind::kAssertProperty),
            1u);
  EXPECT_EQ(CountItemsByKind(r.cu->modules[0]->items,
                             ModuleItemKind::kAssumeProperty),
            1u);
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty),
      1u);
}

TEST(AssertionParsing, NamedAssertInAlways) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always @(posedge clk) begin\n"
              "    check_req: assert property (req |-> ack);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(AssertionParsing, AssertPropertyInAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always @(posedge clk) begin\n"
              "    assert property (req |-> ack);\n"
              "  end\n"
              "endmodule\n"));
}

// --- expect_property_statement ---

TEST(AssertionDeclParsing, ExpectPropertyStatement) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  initial begin\n"
      "    expect (a |-> b) $display(\"pass\"); else $display(\"fail\");\n"
      "  end\n"
      "endmodule\n"));
}

TEST(AssertionDeclParsing, ExpectPropertyStatement_NoActions) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    expect (req |-> ack);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(AssertionParsing, ExpectStatement) {
  auto r = Parse(
      "module top();\n"
      "  logic clk, a, b;\n"
      "  initial begin\n"
      "    expect (@(posedge clk) a ##1 b);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace
