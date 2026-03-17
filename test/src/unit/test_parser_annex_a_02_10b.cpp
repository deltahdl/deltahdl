#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- assertion_item_declaration / property_declaration ---

TEST(AssertionDeclParsing, AssertionItemDecl_PropertyDecl) {
  auto r = Parse(
      "module m;\n"
      "  property p_req;\n"
      "    @(posedge clk) req |-> ack;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "p_req");
}

TEST(AssertionDeclParsing, PropertyDecl_WithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  property p_req;\n"
      "    @(posedge clk) req |-> ##[1:3] ack;\n"
      "  endproperty : p_req\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "p_req");
}

TEST(AssertionDeclParsing, PropertyDecl_WithPortList) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(a, b);\n"
              "    a |-> b;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyDecl_SourceLoc) {
  auto r = Parse(
      "module m;\n"
      "  property my_prop;\n"
      "    a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->loc.IsValid());
}

TEST(AssertionParsing, PropertyDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  property p_req_ack;\n"
      "    @(posedge clk) req |-> ack;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl) {
      found = true;
      EXPECT_EQ(item->name, "p_req_ack");
    }
  }
  EXPECT_TRUE(found);
}

TEST(AssertionParsing, PropertyDeclWithFormals) {
  auto r = Parse(
      "module m;\n"
      "  property p_req_ack(req, ack);\n"
      "    @(posedge clk) req |-> ##[1:3] ack;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* pd =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->name, "p_req_ack");
}

TEST(AssertionParsing, PropertyDeclWithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty : p1\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(AssertionParsing, PropertyWithFormalArgsDecl) {
  auto r = Parse(
      "module m;\n"
      "  property p_valid(signal, valid);\n"
      "    @(posedge clk) signal |-> valid;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionDeclParsing, PropertyAndSequenceDeclsTogether) {
  auto r = Parse(
      "module m;\n"
      "  property p; a; endproperty\n"
      "  sequence s; b; endsequence\n"
      "  assert property (p);\n"
      "  cover sequence (s);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kPropertyDecl),
      nullptr);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kSequenceDecl),
      nullptr);
}

// --- property_port_list / property_port_item ---

TEST(AssertionDeclParsing, PropertyPortItem_DefaultValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(x, y = 1'b1);\n"
              "    x |-> y;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyPortList_Empty) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p();\n"
              "    a |-> b;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyPortItem_LocalInput) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(local input int x);\n"
              "    x > 0;\n"
              "  endproperty\n"
              "endmodule\n"));
}

// --- property_formal_type ---

TEST(AssertionDeclParsing, PropertyFormalType_Property) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(property q);\n"
              "    q;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyFormalType_Sequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(sequence s);\n"
              "    s |-> 1;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyFormalType_Implicit) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(x);\n"
              "    x;\n"
              "  endproperty\n"
              "endmodule\n"));
}

// --- property_spec ---

TEST(AssertionDeclParsing, PropertySpec_ClockingEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertySpec_DisableIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) disable iff (rst) a |-> b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertySpec_DisableIff_ComplexExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) disable iff (rst || !en) req |-> ack);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertySpec_NoClockNoDisable) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (a |-> b);\n"
              "endmodule\n"));
}

TEST(AssertionParsing, AssertPropertyDisableIff) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) disable iff (rst) req |-> ack);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

TEST(AssertionParsing, DisableIffInAssertProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) disable iff (rst) a |-> b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(AssertionParsing, DisableIffInPropertyDecl) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    disable iff (rst == 2)\n"
      "    @(posedge clk) not (a ##1 b);\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(AssertionParsing, DisableIffWithComplexExpr) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) disable iff (rst || !en)\n"
      "    req |-> ##[1:5] ack);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(AssertionParsing, PropertyWithDisableIffDecl) {
  auto r = Parse(
      "module m;\n"
      "  property p_req_ack;\n"
      "    @(posedge clk) disable iff (rst)\n"
      "    req |-> ##[1:3] ack;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- property_instance / property_list_of_arguments / property_actual_arg ---

TEST(AssertionDeclParsing, PropertyInstance_InAssert) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p; a |-> b; endproperty\n"
              "  assert property (p);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyInstance_WithArgs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(x, y); x |-> y; endproperty\n"
              "  assert property (p(a, b));\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyListOfArguments_Positional) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(x, y, z); x |-> y ##1 z; endproperty\n"
              "  assert property (p(a, b, c));\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyListOfArguments_Named) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(x, y); x |-> y; endproperty\n"
              "  assert property (p(.x(a), .y(b)));\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyListOfArguments_Mixed) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(x, y, z); x |-> y ##1 z; endproperty\n"
              "  assert property (p(a, .y(b), .z(c)));\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyActualArg_Expr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(x); x; endproperty\n"
              "  assert property (p(a && b));\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_PropertyInstance) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p; a; endproperty\n"
              "  assert property (@(posedge clk) p);\n"
              "endmodule\n"));
}

TEST(AssertionParsing, AssertWithNamedPropertyInstance) {
  auto r = Parse(
      "module m;\n"
      "  property p_handshake;\n"
      "    @(posedge clk) req |-> ##[1:3] ack;\n"
      "  endproperty\n"
      "  assert property (p_handshake);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* pd =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->name, "p_handshake");
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

TEST(AssertionParsing, PropertyInstanceWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  property p1(a, b);\n"
      "    a |-> ##1 b;\n"
      "  endproperty\n"
      "  assert property (@(posedge clk) p1(req, ack));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

}  // namespace
