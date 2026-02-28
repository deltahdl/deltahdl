// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// pattern ::= ( pattern )
// ---------------------------------------------------------------------------
// §12.6: parenthesized pattern
TEST(ParserA60701, PatternParenthesized) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (e matches (tagged Valid .n)) x = n;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// pattern ::= '{ pattern { , pattern } }
// pattern ::= '{ member_identifier : pattern { , member_identifier : pattern }
// }
// ---------------------------------------------------------------------------
// §12.6: positional assignment pattern in expression context
TEST(ParserA60701, PatternAssignment) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{1, 2, 3};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §12.6: named assignment pattern
TEST(ParserA60701, PatternAssignmentNamed) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{a: 1, b: 2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §10.9: assignment pattern with dot-identifier pattern bindings
TEST(ParserA60701, PatternAssignmentWithDotBindings) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(s) matches\n"
      "      '{.a, .b}: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// assignment_pattern ::= '{ constant_expression { expression { , expression } }
// }
// ---------------------------------------------------------------------------
// §10.9.1: replication form of assignment pattern
TEST(ParserA60701, AssignmentPatternReplication) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{4{8'd0}};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §10.9.1: replication form with multiple elements
TEST(ParserA60701, AssignmentPatternReplicationMultiElem) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{2{a, b}};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// assignment_pattern_expression ::= [ type ] assignment_pattern
// assignment_pattern_expression_type ::=
//   ps_type_identifier | ps_parameter_identifier | integer_atom_type |
//   type_reference
// ---------------------------------------------------------------------------
// §10.9: typed assignment pattern expression with user-defined type
TEST(ParserA60701, AssignmentPatternWithType) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  initial begin\n"
      "    pair_t p;\n"
      "    p = pair_t'{a: 8'd1, b: 8'd2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §10.9: typed assignment pattern expression with integer_atom_type
TEST(ParserA60701, AssignmentPatternWithIntegerAtomType) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = int'{31: 1, default: 0};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// structure_pattern_key ::= member_identifier | assignment_pattern_key
// array_pattern_key ::= constant_expression | assignment_pattern_key
// assignment_pattern_key ::= simple_type | default
// ---------------------------------------------------------------------------
// §10.9: assignment_pattern_key with default
TEST(ParserA60701, PatternKeyDefault) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{default: 0};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §10.9: structure_pattern_key with member identifier and default
TEST(ParserA60701, StructurePatternKeyMemberAndDefault) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{a: 5, default: 0};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §10.9: array_pattern_key with constant_expression
TEST(ParserA60701, ArrayPatternKeyConstExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{0: 8'd1, 1: 8'd2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// assignment_pattern_net_lvalue ::= '{ net_lvalue { , net_lvalue } }
// assignment_pattern_variable_lvalue ::= '{ variable_lvalue { , variable_lvalue
// } }
// ---------------------------------------------------------------------------
// §10.9: assignment pattern as LHS (variable lvalue)
TEST(ParserA60701, AssignmentPatternVariableLvalue) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    '{a, b, c} = '{1, 2, 3};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// case_pattern_item ::= pattern [ &&& expression ] : statement_or_null
// ---------------------------------------------------------------------------
// §12.6.1: case pattern item with &&& guard
TEST(ParserA60701, CasePatternItemWithGuard) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) matches\n"
      "      .n &&& (n > 0): y = n;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §12.6.1: case-matches with tagged pattern and &&& guard
TEST(ParserA60701, CasePatternTaggedWithGuard) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(instr) matches\n"
      "      tagged Add '{.r1, .r2, .rd} &&& (rd != 0): x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §12.6.1: case-matches with default item
TEST(ParserA60701, CaseMatchesDefault) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) matches\n"
      "      5: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_EQ(stmt->case_items.size(), 2u);
  EXPECT_TRUE(stmt->case_items[1].is_default);
}

// §12.6.1: case-matches with multiple pattern items
TEST(ParserA60701, CaseMatchesMultipleItems) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) matches\n"
      "      1: y = 10;\n"
      "      2: y = 20;\n"
      "      3: y = 30;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->case_items.size(), 4u);
}

// ---------------------------------------------------------------------------
// Parsing: matches as binary expression operator
// ---------------------------------------------------------------------------
// §12.6.2: matches operator in if-condition
TEST(ParserA60701, MatchesExprInIfCondition) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x matches 5) y = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->condition->op, TokenKind::kKwMatches);
}

// §12.6.2: matches with &&& operator in if-condition
TEST(ParserA60701, MatchesWithTripleAndInIf) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x matches 5 &&& en) y = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// AST structure: assignment pattern elements and keys
// ---------------------------------------------------------------------------
// §10.9: positional assignment pattern — AST elements count
TEST(ParserA60701, AssignmentPatternElementsCount) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{1, 2, 3, 4};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements.size(), 4u);
}

// §10.9: named assignment pattern — AST pattern_keys populated
TEST(ParserA60701, AssignmentPatternKeysPopulated) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{a: 1, b: 2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(rhs->pattern_keys.size(), 2u);
  EXPECT_EQ(rhs->pattern_keys[0], "a");
  EXPECT_EQ(rhs->pattern_keys[1], "b");
  EXPECT_EQ(rhs->elements.size(), 2u);
}

// §10.9: replication pattern — AST repeat_count set
TEST(ParserA60701, ReplicationPatternRepeatCount) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{3{8'd5}};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(rhs->elements.size(), 1u);
  // The replication element is a kReplicate expression
  auto* rep = rhs->elements[0];
  EXPECT_EQ(rep->kind, ExprKind::kReplicate);
  EXPECT_NE(rep->repeat_count, nullptr);
}

// §12.6: tagged expression — AST kind is kTagged
TEST(ParserA60701, TaggedExprAstKind) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = tagged Valid 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTagged);
  // member identifier stored in rhs->rhs
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->text, "Valid");
}

// §10.9: empty assignment pattern '{} parses
TEST(ParserA60701, EmptyAssignmentPattern) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements.size(), 0u);
}

// =============================================================================
// A.6.8 Looping statements — loop_statement
// =============================================================================
// --- forever statement_or_null ---
TEST(ParserA608, ForeverLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin forever #5 clk = ~clk; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(ParserA608, ForeverNullStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin forever ; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
}

// --- repeat ( expression ) statement_or_null ---
TEST(ParserA608, RepeatLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin repeat (10) @(posedge clk); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRepeat);
  EXPECT_NE(stmt->condition, nullptr);
}

TEST(ParserA608, RepeatNullStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin repeat (5) ; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRepeat);
}

// --- while ( expression ) statement_or_null ---
TEST(ParserA608, WhileLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin while (x > 0) x = x - 1; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(ParserA608, WhileNullStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin while (x > 0) ; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
}

// --- for ( [for_initialization] ; [expression] ; [for_step] ) stmt_or_null ---
TEST(ParserA608, ForLoopParse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
}

TEST(ParserA608, ForLoopParts) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->for_init, nullptr);
  EXPECT_NE(stmt->for_cond, nullptr);
  EXPECT_NE(stmt->for_step, nullptr);
  EXPECT_NE(stmt->for_body, nullptr);
}

TEST(ParserA608, ForLoopTypedInit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kInt);
}

TEST(ParserA608, ForLoopUntypedInit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kImplicit);
}

// §A.6.8: for_initialization is optional — empty init
TEST(ParserA608, ForEmptyInit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init, nullptr);
}

// §A.6.8: expression in for condition is optional — empty cond
TEST(ParserA608, ForEmptyCond) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; ; i++) begin\n"
      "      if (i == 10) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_cond, nullptr);
}

// §A.6.8: for_step is optional — empty step
TEST(ParserA608, ForEmptyStep) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10;) begin\n"
      "      i = i + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_step, nullptr);
}

// §A.6.8: all three for parts optional — for (;;)
TEST(ParserA608, ForAllEmpty) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (;;) break;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init, nullptr);
  EXPECT_EQ(stmt->for_cond, nullptr);
  EXPECT_EQ(stmt->for_step, nullptr);
}

TEST(ParserA608, ForNullStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
}

// --- for_variable_declaration: [var] data_type variable_identifier = expr ---
TEST(ParserA608, ForVarKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (var int i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kInt);
}

TEST(ParserA608, ForLogicTypeInit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (logic [7:0] i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kLogic);
}

// --- for_step_assignment: operator_assignment ---
TEST(ParserA608, ForStepCompoundAssign) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i += 1) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_step, nullptr);
}

// --- for_step_assignment: inc_or_dec_expression ---
TEST(ParserA608, ForStepPostIncrement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->for_step, nullptr);
}

TEST(ParserA608, ForStepPreIncrement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; ++i) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->for_step, nullptr);
}

TEST(ParserA608, ForStepPostDecrement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 10; i > 0; i--) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->for_step, nullptr);
}

// --- do statement_or_null while ( expression ) ; ---
TEST(ParserA608, DoWhileLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin do x = x - 1; while (x > 0); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(ParserA608, DoWhileNullStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin do ; while (x > 0); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
}

TEST(ParserA608, DoWhileBlockBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    do begin x = x + 1; end while (x < 10);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

// --- foreach ( ps_or_hierarchical_array_identifier [loop_variables] ) stmt ---
TEST(ParserA608, ForeachStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foreach (arr[i]) $display(arr[i]); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_NE(stmt->expr, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(ParserA608, ForeachSingleVar) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foreach (arr[i]) x = i; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->foreach_vars.size(), 1u);
  EXPECT_EQ(stmt->foreach_vars[0], "i");
}

// §A.6.8: loop_variables — multiple comma-separated identifiers
TEST(ParserA608, ForeachMultipleVars) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foreach (matrix[i, j]) x = i; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->foreach_vars.size(), 2u);
  EXPECT_EQ(stmt->foreach_vars[0], "i");
  EXPECT_EQ(stmt->foreach_vars[1], "j");
}

// §A.6.8: loop_variables — empty slots (skipped dimensions)
TEST(ParserA608, ForeachEmptyVarSlot) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foreach (arr[, j]) x = j; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->foreach_vars.size(), 2u);
  EXPECT_TRUE(stmt->foreach_vars[0].empty());
  EXPECT_EQ(stmt->foreach_vars[1], "j");
}

// §A.6.8: ps_or_hierarchical_array_identifier — hierarchical name
TEST(ParserA608, ForeachHierarchicalArray) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foreach (obj.arr[i]) x = i; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kMemberAccess);
}

TEST(ParserA608, ForeachBlockBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    foreach (arr[i]) begin\n"
      "      x = arr[i];\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

}  // namespace
