// §16.12: Declaring properties

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem *FindItemByKind(const std::vector<ModuleItem *> &items,
                                  ModuleItemKind kind) {
  for (auto *item : items) {
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
  auto *item =
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
  auto *item =
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
  auto *item =
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

}  // namespace
