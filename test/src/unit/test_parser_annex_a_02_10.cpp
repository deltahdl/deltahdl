#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem* FindItemByKind(const std::vector<ModuleItem*>& items,
                                  ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

// =============================================================================
// §A.2.10 Production #1: concurrent_assertion_item
// concurrent_assertion_item ::=
//     [ block_identifier : ] concurrent_assertion_statement
//   | checker_instantiation
// =============================================================================

TEST(ParserA210, ConcurrentAssertionItem_AssertProperty) {
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

TEST(ParserA210, ConcurrentAssertionItem_AssumeProperty) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) req |-> ack);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(item, nullptr);
}

TEST(ParserA210, ConcurrentAssertionItem_CoverProperty) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty);
  ASSERT_NE(item, nullptr);
}

// =============================================================================
// §A.2.10 Production #2: concurrent_assertion_statement
// concurrent_assertion_statement ::=
//     assert_property_statement | assume_property_statement
//   | cover_property_statement  | cover_sequence_statement
//   | restrict_property_statement
// =============================================================================

// Productions #3-#5 tested above (assert/assume/cover property).

// =============================================================================
// §A.2.10 Production #6: expect_property_statement
// expect_property_statement ::= expect ( property_spec ) action_block
// =============================================================================

TEST(ParserA210, ExpectPropertyStatement) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  initial begin\n"
      "    expect (a |-> b) $display(\"pass\"); else $display(\"fail\");\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserA210, ExpectPropertyStatement_NoActions) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    expect (req |-> ack);\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #7: cover_sequence_statement
// cover_sequence_statement ::=
//     cover sequence ( [clocking_event] [disable iff (expr)] sequence_expr )
//     statement_or_null
// =============================================================================

TEST(ParserA210, CoverSequence_Basic) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverSequence);
  ASSERT_NE(item, nullptr);
}

TEST(ParserA210, CoverSequence_WithPassAction) {
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

TEST(ParserA210, CoverSequence_WithDisableIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  cover sequence (@(posedge clk) disable iff (rst) a ##1 b);\n"
              "endmodule\n"));
}

TEST(ParserA210, CoverSequence_Kind) {
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

// =============================================================================
// §A.2.10 Production #8: restrict_property_statement
// restrict_property_statement ::= restrict property ( property_spec ) ;
// =============================================================================

TEST(ParserA210, RestrictProperty_Basic) {
  auto r = Parse(
      "module m;\n"
      "  restrict property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r.cu->modules[0]->items,
                              ModuleItemKind::kRestrictProperty);
  ASSERT_NE(item, nullptr);
}

TEST(ParserA210, RestrictProperty_Kind) {
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

TEST(ParserA210, RestrictProperty_WithDisableIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  restrict property (\n"
              "    @(posedge clk) disable iff (rst) a |-> b);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #3: assert_property_statement
// assert_property_statement ::= assert property ( property_spec ) action_block
// =============================================================================

TEST(ParserA210, AssertProperty_WithActionBlock) {
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

TEST(ParserA210, AssertProperty_PassOnly) {
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

TEST(ParserA210, AssertProperty_FailOnly) {
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

// =============================================================================
// §A.2.10 Production #4: assume_property_statement
// =============================================================================

TEST(ParserA210, AssumeProperty_WithElseAction) {
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

// =============================================================================
// §A.2.10 Production #5: cover_property_statement
// =============================================================================

TEST(ParserA210, CoverProperty_WithPassStmt) {
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

// =============================================================================
// §A.2.10 Production #9: property_instance
// property_instance ::=
//     ps_or_hierarchical_property_identifier [ ( [property_list_of_arguments] )
//     ]
// =============================================================================

TEST(ParserA210, PropertyInstance_InAssert) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p; a |-> b; endproperty\n"
              "  assert property (p);\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyInstance_WithArgs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(x, y); x |-> y; endproperty\n"
              "  assert property (p(a, b));\n"
              "endmodule\n"));
}

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

TEST(ParserA210, PropertyListOfArguments_Named) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(x, y); x |-> y; endproperty\n"
              "  assert property (p(.x(a), .y(b)));\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #11: property_actual_arg
// property_actual_arg ::= property_expr | sequence_actual_arg
// =============================================================================

TEST(ParserA210, PropertyActualArg_Expr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(x); x; endproperty\n"
              "  assert property (p(a && b));\n"
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

TEST(ParserA210, AssertionItemDecl_SequenceDecl) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_handshake;\n"
      "    req ##[1:3] ack;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "s_handshake");
}

TEST(ParserA210, AssertionItemDecl_LetDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let max(a, b) = (a > b) ? a : b;\n"
              "endmodule\n"));
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

// =============================================================================
// §A.2.10 Productions #14-#16: property_port_list, property_port_item,
//     property_lvar_port_direction
// property_port_item ::=
//     { attribute_instance } [ local [ property_lvar_port_direction ] ]
//     property_formal_type formal_port_identifier { variable_dimension }
//     [ = property_actual_arg ]
// property_lvar_port_direction ::= input
// =============================================================================

TEST(ParserA210, PropertyPortItem_LocalInput) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(local input int x);\n"
              "    x > 0;\n"
              "  endproperty\n"
              "endmodule\n"));
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
// §A.2.10 Production #17: property_formal_type
// property_formal_type ::= sequence_formal_type | property
// =============================================================================

TEST(ParserA210, PropertyFormalType_Property) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(property q);\n"
              "    q;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyFormalType_Sequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(sequence s);\n"
              "    s |-> 1;\n"
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

// =============================================================================
// §A.2.10 Production #19: property_expr — many alternatives
// =============================================================================

// property_expr ::= sequence_expr
TEST(ParserA210, PropertyExpr_SequenceExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##1 b);\n"
              "endmodule\n"));
}

// property_expr ::= strong ( sequence_expr )
TEST(ParserA210, PropertyExpr_Strong) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) strong(a ##1 b));\n"
              "endmodule\n"));
}

// property_expr ::= weak ( sequence_expr )
TEST(ParserA210, PropertyExpr_Weak) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) weak(a ##1 b));\n"
              "endmodule\n"));
}

// property_expr ::= ( property_expr )
TEST(ParserA210, PropertyExpr_Parenthesized) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) (a |-> b));\n"
              "endmodule\n"));
}

// property_expr ::= not property_expr
TEST(ParserA210, PropertyExpr_Not) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) not a);\n"
              "endmodule\n"));
}

// property_expr ::= property_expr or property_expr
TEST(ParserA210, PropertyExpr_Or) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a or b);\n"
              "endmodule\n"));
}

// property_expr ::= property_expr and property_expr
TEST(ParserA210, PropertyExpr_And) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a and b);\n"
              "endmodule\n"));
}

// property_expr ::= sequence_expr |-> property_expr
TEST(ParserA210, PropertyExpr_OverlappedImplication) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) req |-> ack);\n"
              "endmodule\n"));
}

// property_expr ::= sequence_expr |=> property_expr
TEST(ParserA210, PropertyExpr_NonOverlappedImplication) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) req |=> ack);\n"
              "endmodule\n"));
}

// property_expr ::= if (...) property_expr [else property_expr]
TEST(ParserA210, PropertyExpr_IfElse) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    if (mode) a |-> b else c |-> d);\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyExpr_IfNoElse) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    if (mode) a |-> b);\n"
              "endmodule\n"));
}

// property_expr ::= case (...) property_case_item ... endcase
TEST(ParserA210, PropertyExpr_Case) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    case (sel)\n"
              "      2'b00: a |-> b;\n"
              "      2'b01: c |-> d;\n"
              "      default: 1;\n"
              "    endcase);\n"
              "endmodule\n"));
}

// property_expr ::= sequence_expr #-# property_expr
TEST(ParserA210, PropertyExpr_FollowedByOverlapped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a #-# b);\n"
              "endmodule\n"));
}

// property_expr ::= sequence_expr #=# property_expr
TEST(ParserA210, PropertyExpr_FollowedByNonOverlapped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a #=# b);\n"
              "endmodule\n"));
}

// property_expr ::= nexttime property_expr
TEST(ParserA210, PropertyExpr_Nexttime) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) nexttime a);\n"
              "endmodule\n"));
}

// property_expr ::= nexttime [ constant_expression ] property_expr
TEST(ParserA210, PropertyExpr_NexttimeWithCount) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) nexttime [3] a);\n"
              "endmodule\n"));
}

// property_expr ::= s_nexttime property_expr
TEST(ParserA210, PropertyExpr_SNexttime) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) s_nexttime a);\n"
              "endmodule\n"));
}

// property_expr ::= s_nexttime [ constant_expression ] property_expr
TEST(ParserA210, PropertyExpr_SNexttimeWithCount) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) s_nexttime [2] a);\n"
              "endmodule\n"));
}

// property_expr ::= always property_expr
TEST(ParserA210, PropertyExpr_Always) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) always a);\n"
              "endmodule\n"));
}

// property_expr ::= always [ cycle_delay_const_range_expression ] property_expr
TEST(ParserA210, PropertyExpr_AlwaysRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) always [0:5] a);\n"
              "endmodule\n"));
}

// property_expr ::= s_always [ constant_range ] property_expr
TEST(ParserA210, PropertyExpr_SAlways) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) s_always [0:$] a);\n"
              "endmodule\n"));
}

// property_expr ::= s_eventually property_expr
TEST(ParserA210, PropertyExpr_SEventually) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) s_eventually a);\n"
              "endmodule\n"));
}

// property_expr ::= s_eventually [ cycle_delay_const_range_expression ]
// property_expr
TEST(ParserA210, PropertyExpr_SEventuallyRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) s_eventually [1:5] a);\n"
              "endmodule\n"));
}

// property_expr ::= eventually [ constant_range ] property_expr
TEST(ParserA210, PropertyExpr_Eventually) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) eventually [1:5] a);\n"
              "endmodule\n"));
}

// property_expr ::= property_expr until property_expr
TEST(ParserA210, PropertyExpr_Until) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a until b);\n"
              "endmodule\n"));
}

// property_expr ::= property_expr s_until property_expr
TEST(ParserA210, PropertyExpr_SUntil) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a s_until b);\n"
              "endmodule\n"));
}

// property_expr ::= property_expr until_with property_expr
TEST(ParserA210, PropertyExpr_UntilWith) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a until_with b);\n"
              "endmodule\n"));
}

// property_expr ::= property_expr s_until_with property_expr
TEST(ParserA210, PropertyExpr_SUntilWith) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a s_until_with b);\n"
              "endmodule\n"));
}

// property_expr ::= property_expr implies property_expr
TEST(ParserA210, PropertyExpr_Implies) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a implies b);\n"
              "endmodule\n"));
}

// property_expr ::= property_expr iff property_expr
TEST(ParserA210, PropertyExpr_Iff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a iff b);\n"
              "endmodule\n"));
}

// property_expr ::= accept_on ( expression_or_dist ) property_expr
TEST(ParserA210, PropertyExpr_AcceptOn) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  assert property (@(posedge clk) accept_on(done) req |-> ack);\n"
      "endmodule\n"));
}

// property_expr ::= reject_on ( expression_or_dist ) property_expr
TEST(ParserA210, PropertyExpr_RejectOn) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) reject_on(err) req |-> ack);\n"
              "endmodule\n"));
}

// property_expr ::= sync_accept_on ( expression_or_dist ) property_expr
TEST(ParserA210, PropertyExpr_SyncAcceptOn) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) sync_accept_on(done) req |-> ack);\n"
              "endmodule\n"));
}

// property_expr ::= sync_reject_on ( expression_or_dist ) property_expr
TEST(ParserA210, PropertyExpr_SyncRejectOn) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) sync_reject_on(err) req |-> ack);\n"
              "endmodule\n"));
}

// property_expr ::= property_instance
TEST(ParserA210, PropertyExpr_PropertyInstance) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p; a; endproperty\n"
              "  assert property (@(posedge clk) p);\n"
              "endmodule\n"));
}

// property_expr ::= clocking_event property_expr
TEST(ParserA210, PropertyExpr_ClockingEventPropertyExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) a |-> @(posedge clk2) b);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #20: property_case_item
// property_case_item ::=
//     expression_or_dist { , expression_or_dist } : property_expr ;
//   | default [ : ] property_expr ;
// =============================================================================

TEST(ParserA210, PropertyCaseItem_MultiExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    case (sel)\n"
              "      2'b00, 2'b01: a |-> b;\n"
              "      default: 1;\n"
              "    endcase);\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyCaseItem_DefaultOnly) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    case (sel)\n"
              "      default: a;\n"
              "    endcase);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #21: sequence_declaration
// sequence_declaration ::=
//     sequence sequence_identifier [ ( [sequence_port_list] ) ] ;
//     { assertion_variable_declaration }
//     sequence_expr [ ; ]
//     endsequence [ : sequence_identifier ]
// =============================================================================

TEST(ParserA210, SequenceDecl_WithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_req;\n"
      "    req ##[1:3] ack;\n"
      "  endsequence : s_req\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "s_req");
}

TEST(ParserA210, SequenceDecl_WithPortList) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b);\n"
              "    a ##1 b;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceDecl_SourceLoc) {
  auto r = Parse(
      "module m;\n"
      "  sequence my_seq;\n"
      "    a;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->loc.IsValid());
}

// =============================================================================
// §A.2.10 Productions #22-#23: sequence_port_list, sequence_port_item
// sequence_port_item ::=
//     { attribute_instance } [ local [ sequence_lvar_port_direction ] ]
//     sequence_formal_type formal_port_identifier { variable_dimension }
//     [ = sequence_actual_arg ]
// =============================================================================

TEST(ParserA210, SequencePortItem_LocalInout) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(local inout int x);\n"
              "    x > 0;\n"
              "  endsequence\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #24: sequence_lvar_port_direction
// sequence_lvar_port_direction ::= input | inout | output
// =============================================================================

TEST(ParserA210, SequenceLvarPortDirection_Input) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(local input int x);\n"
              "    x;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceLvarPortDirection_Output) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(local output int x);\n"
              "    (1, x = a) ##1 (1, x = b);\n"
              "  endsequence\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #25: sequence_formal_type
// sequence_formal_type ::= data_type_or_implicit | sequence | untyped
// =============================================================================

TEST(ParserA210, SequenceFormalType_Sequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(sequence sub_seq);\n"
              "    sub_seq ##1 a;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceFormalType_Untyped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(untyped x);\n"
              "    x ##1 a;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceFormalType_DataType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(int x);\n"
              "    x > 0;\n"
              "  endsequence\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #26: sequence_expr — many alternatives
// =============================================================================

// sequence_expr ::= cycle_delay_range sequence_expr ...
TEST(ParserA210, SequenceExpr_CycleDelay) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) ##2 a);\n"
              "endmodule\n"));
}

// sequence_expr ::= sequence_expr cycle_delay_range sequence_expr ...
TEST(ParserA210, SequenceExpr_Concatenation) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##1 b ##2 c);\n"
              "endmodule\n"));
}

// sequence_expr ::= expression_or_dist [ boolean_abbrev ]
TEST(ParserA210, SequenceExpr_ExprWithBooleanAbbrev) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*3]);\n"
              "endmodule\n"));
}

// sequence_expr ::= ( sequence_expr {, sequence_match_item} ) [sequence_abbrev]
TEST(ParserA210, SequenceExpr_ParenWithMatchItems) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b, x = c) |-> d);\n"
              "endmodule\n"));
}

// sequence_expr ::= sequence_expr and sequence_expr
TEST(ParserA210, SequenceExpr_And) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a and b);\n"
              "endmodule\n"));
}

// sequence_expr ::= sequence_expr intersect sequence_expr
TEST(ParserA210, SequenceExpr_Intersect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b) intersect (c ##1 d));\n"
              "endmodule\n"));
}

// sequence_expr ::= sequence_expr or sequence_expr
TEST(ParserA210, SequenceExpr_Or) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a or b);\n"
              "endmodule\n"));
}

// sequence_expr ::= first_match ( sequence_expr {, sequence_match_item} )
TEST(ParserA210, SequenceExpr_FirstMatch) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    first_match(a ##[1:5] b));\n"
              "endmodule\n"));
}

// sequence_expr ::= expression_or_dist throughout sequence_expr
TEST(ParserA210, SequenceExpr_Throughout) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    en throughout (a ##1 b ##1 c));\n"
              "endmodule\n"));
}

// sequence_expr ::= sequence_expr within sequence_expr
TEST(ParserA210, SequenceExpr_Within) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b) within (c ##[1:5] d));\n"
              "endmodule\n"));
}

// sequence_expr ::= clocking_event sequence_expr
TEST(ParserA210, SequenceExpr_ClockingEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a |-> @(negedge clk) b);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #27: cycle_delay_range
// cycle_delay_range ::=
//     ## constant_primary
//   | ## [ cycle_delay_const_range_expression ]
//   | ##[*]
//   | ##[+]
// =============================================================================

TEST(ParserA210, CycleDelayRange_Constant) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##1 b);\n"
              "endmodule\n"));
}

TEST(ParserA210, CycleDelayRange_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##[1:5] b);\n"
              "endmodule\n"));
}

TEST(ParserA210, CycleDelayRange_OpenEndRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##[1:$] b);\n"
              "endmodule\n"));
}

TEST(ParserA210, CycleDelayRange_Star) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) ##[*] a);\n"
              "endmodule\n"));
}

TEST(ParserA210, CycleDelayRange_Plus) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) ##[+] a);\n"
              "endmodule\n"));
}

TEST(ParserA210, CycleDelayRange_Zero) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##0 b);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #28: sequence_method_call
// sequence_method_call ::= sequence_instance . method_identifier
// =============================================================================

TEST(ParserA210, SequenceMethodCall_Triggered) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s.triggered |-> c);\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceMethodCall_Matched) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s.matched |-> c);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #29: sequence_match_item
// sequence_match_item ::=
//     operator_assignment | inc_or_dec_expression | subroutine_call
// =============================================================================

TEST(ParserA210, SequenceMatchItem_Assignment) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b, x = c) |-> d);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #30: sequence_instance
// sequence_instance ::=
//     ps_or_hierarchical_sequence_identifier
//     [ ( [sequence_list_of_arguments] ) ]
// =============================================================================

TEST(ParserA210, SequenceInstance_InProperty) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##1 b; endsequence\n"
              "  property p; s |-> c; endproperty\n"
              "  assert property (p);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #31: sequence_list_of_arguments
// =============================================================================

TEST(ParserA210, SequenceListOfArguments_Positional) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b); a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s(x, y));\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #32: sequence_actual_arg
// sequence_actual_arg ::= event_expression | sequence_expr | $
// =============================================================================

TEST(ParserA210, SequenceActualArg_Dollar) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b); a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s(x, $));\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #33: boolean_abbrev
// boolean_abbrev ::=
//     consecutive_repetition | nonconsecutive_repetition | goto_repetition
// =============================================================================

// §A.2.10 Production #34: sequence_abbrev
// sequence_abbrev ::= consecutive_repetition

// §A.2.10 Production #35: consecutive_repetition
// consecutive_repetition ::= [* const_or_range_expression ] | [*] | [+]

TEST(ParserA210, ConsecutiveRepetition_Exact) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*3] |-> b);\n"
              "endmodule\n"));
}

TEST(ParserA210, ConsecutiveRepetition_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*1:3] |-> b);\n"
              "endmodule\n"));
}

TEST(ParserA210, ConsecutiveRepetition_Star) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*] ##1 b);\n"
              "endmodule\n"));
}

TEST(ParserA210, ConsecutiveRepetition_Plus) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [+] ##1 b);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #36: nonconsecutive_repetition
// nonconsecutive_repetition ::= [= const_or_range_expression ]
// =============================================================================

TEST(ParserA210, NonconsecutiveRepetition) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [=3] |-> b);\n"
              "endmodule\n"));
}

TEST(ParserA210, NonconsecutiveRepetition_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [=1:3] |-> b);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #37: goto_repetition
// goto_repetition ::= [-> const_or_range_expression ]
// =============================================================================

TEST(ParserA210, GotoRepetition_Exact) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [->2] |-> b);\n"
              "endmodule\n"));
}

TEST(ParserA210, GotoRepetition_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [->1:3] |-> b);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #38: const_or_range_expression
// const_or_range_expression ::=
//     constant_expression | cycle_delay_const_range_expression
// =============================================================================

TEST(ParserA210, ConstOrRangeExpr_Constant) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*5]);\n"
              "endmodule\n"));
}

TEST(ParserA210, ConstOrRangeExpr_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*2:8]);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #39: cycle_delay_const_range_expression
// cycle_delay_const_range_expression ::=
//     constant_expression : constant_expression
//   | constant_expression : $
// =============================================================================

TEST(ParserA210, CycleDelayConstRange_FiniteRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##[2:5] b);\n"
              "endmodule\n"));
}

TEST(ParserA210, CycleDelayConstRange_OpenEnd) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##[1:$] b);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #40: assertion_variable_declaration
// assertion_variable_declaration ::=
//     var_data_type list_of_variable_decl_assignments ;
// =============================================================================

TEST(ParserA210, AssertionVariableDecl_InProperty) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p;\n"
              "    int x;\n"
              "    (a, x = b) |-> (c == x);\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(ParserA210, AssertionVariableDecl_InSequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s;\n"
              "    int x;\n"
              "    (a, x = b) ##1 (c == x);\n"
              "  endsequence\n"
              "endmodule\n"));
}

// =============================================================================
// Additional AST verification tests
// =============================================================================

TEST(ParserA210, AllFiveConcurrentAssertionTypes) {
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

TEST(ParserA210, PropertyAndSequenceDeclsTogether) {
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

TEST(ParserA210, RestrictProperty_HasAssertExpr) {
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

TEST(ParserA210, CoverSequence_HasAssertExpr) {
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

// =============================================================================
// Gap-filling tests identified by coverage proof
// =============================================================================

// concurrent_assertion_item ::= [ block_identifier : ]
// concurrent_assertion_statement
TEST(ParserA210, ConcurrentAssertionItem_Labeled) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always @(posedge clk) begin\n"
              "    my_check: assert(a == b);\n"
              "  end\n"
              "endmodule\n"));
}

// sequence_match_item ::= inc_or_dec_expression
TEST(ParserA210, SequenceMatchItem_IncDec) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b, x++) |-> c);\n"
              "endmodule\n"));
}

// sequence_match_item ::= subroutine_call
TEST(ParserA210, SequenceMatchItem_SubroutineCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b, $display(\"match\")) |-> c);\n"
              "endmodule\n"));
}

// sequence_list_of_arguments — named arguments
TEST(ParserA210, SequenceListOfArguments_Named) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b); a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s(.a(x), .b(y)));\n"
              "endmodule\n"));
}

// property_list_of_arguments — mixed positional + named
TEST(ParserA210, PropertyListOfArguments_Mixed) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(x, y, z); x |-> y ##1 z; endproperty\n"
              "  assert property (p(a, .y(b), .z(c)));\n"
              "endmodule\n"));
}

// sequence_actual_arg ::= event_expression
TEST(ParserA210, SequenceActualArg_EventExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b); a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s(posedge x, y));\n"
              "endmodule\n"));
}

// assume_property_statement with no action block
TEST(ParserA210, AssumeProperty_NoActionBlock) {
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

// property_port_list — empty port list
TEST(ParserA210, PropertyPortList_Empty) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p();\n"
              "    a |-> b;\n"
              "  endproperty\n"
              "endmodule\n"));
}

// sequence_port_item with default value
TEST(ParserA210, SequencePortItem_DefaultValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b = 1'b1);\n"
              "    a ##1 b;\n"
              "  endsequence\n"
              "endmodule\n"));
}

// sequence_instance with sequence_abbrev
TEST(ParserA210, SequenceExpr_SequenceInstanceWithAbbrev) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s [*3] |-> c);\n"
              "endmodule\n"));
}

// sequence_list_of_arguments — mixed positional + named
TEST(ParserA210, SequenceListOfArguments_Mixed) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b, c); a ##1 b ##1 c; endsequence\n"
              "  assert property (@(posedge clk) s(x, .b(y), .c(z)));\n"
              "endmodule\n"));
}

// assertion_variable_declaration — multiple vars and complex type
TEST(ParserA210, AssertionVariableDecl_MultipleVars) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p;\n"
              "    int x;\n"
              "    logic [7:0] y;\n"
              "    (a, x = b) |-> (c == x);\n"
              "  endproperty\n"
              "endmodule\n"));
}

// property_case_item — default without colon
TEST(ParserA210, PropertyCaseItem_DefaultNoColon) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    case (sel)\n"
              "      2'b00: a |-> b;\n"
              "      default a;\n"
              "    endcase);\n"
              "endmodule\n"));
}

// property_formal_type — implicit (no type)
TEST(ParserA210, PropertyFormalType_Implicit) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(x);\n"
              "    x;\n"
              "  endproperty\n"
              "endmodule\n"));
}

}  // namespace
