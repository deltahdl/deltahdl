// §16.12: Declaring properties

#include "fixture_parser.h"

using namespace delta;

static ModuleItem* FindItemByKind(const std::vector<ModuleItem*>& items,
                                  ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

namespace {

// =============================================================================
// §A.2.10 Production #10: property_list_of_arguments
// property_list_of_arguments ::=
//     [property_actual_arg] { , [property_actual_arg] }
//         { , . identifier ( [property_actual_arg] ) }
//   | . identifier ( [property_actual_arg] )
//         { , . identifier ( [property_actual_arg] ) }
// =============================================================================
TEST(ParserA210, PropertyListOfArguments_Positional) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(x, y, z); x |-> y ##1 z; endproperty\n"
              "  assert property (p(a, b, c));\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #12: assertion_item_declaration
// assertion_item_declaration ::=
//     property_declaration | sequence_declaration | let_declaration
// =============================================================================
TEST(ParserA210, AssertionItemDecl_PropertyDecl) {
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

// =============================================================================
// §A.2.10 Production #13: property_declaration
// property_declaration ::=
//     property property_identifier [ ( [property_port_list] ) ] ;
//     { assertion_variable_declaration }
//     property_spec [ ; ]
//     endproperty [ : property_identifier ]
// =============================================================================
TEST(ParserA210, PropertyDecl_WithEndLabel) {
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

TEST(ParserA210, PropertyDecl_WithPortList) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(a, b);\n"
              "    a |-> b;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyDecl_SourceLoc) {
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

TEST(ParserA210, PropertyPortItem_DefaultValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(x, y = 1'b1);\n"
              "    x |-> y;\n"
              "  endproperty\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #18: property_spec
// property_spec ::=
//     [clocking_event] [disable iff (expression_or_dist)] property_expr
// =============================================================================
TEST(ParserA210, PropertySpec_ClockingEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a);\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertySpec_DisableIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) disable iff (rst) a |-> b);\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertySpec_DisableIff_ComplexExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) disable iff (rst || !en) req |-> ack);\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertySpec_NoClockNoDisable) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (a |-> b);\n"
              "endmodule\n"));
}

// property_port_list — empty port list
TEST(ParserA210, PropertyPortList_Empty) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p();\n"
              "    a |-> b;\n"
              "  endproperty\n"
              "endmodule\n"));
}

// --- Test helpers ---
struct ParseResult16b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult16b Parse(const std::string& src) {
  ParseResult16b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// §16.12 Property declarations
// =============================================================================
TEST(ParserSection16, PropertyDeclaration) {
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

struct ParseResult16c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult16c Parse(const std::string& src) {
  ParseResult16c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

using VerifyParseTest = ProgramTestParse;

// =============================================================================
// Section 16.5.1 -- disable iff in concurrent assertions
// =============================================================================
// Assert property with disable iff.
TEST(ParserSection16, Sec16_5_1_AssertPropertyDisableIff) {
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

TEST(ParserAnnexF, AnnexFPropertyDecl) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    @(posedge clk) a |-> ##1 b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl) {
      found = true;
      EXPECT_EQ(item->name, "p1");
    }
  }
  EXPECT_TRUE(found);
}

// =============================================================================
// §16.12 Property declarations — with formal arguments
// =============================================================================
TEST(ParserSection16, PropertyDeclWithFormals) {
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

TEST(ParserSection16, PropertyDeclWithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty : p1\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// §16.13.6 Disable iff
// =============================================================================
TEST(ParserSection16, DisableIffInAssertProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) disable iff (rst) a |-> b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, DisableIffInPropertyDecl) {
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

}  // namespace
