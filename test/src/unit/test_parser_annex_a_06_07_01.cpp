#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

namespace {

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

static Stmt *FirstInitialStmt(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

struct SimA60701Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src,
                                 SimA60701Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

}  // namespace

// =============================================================================
// A.6.7.1 Patterns — Parsing tests
// =============================================================================

// ---------------------------------------------------------------------------
// pattern ::= constant_expression
// ---------------------------------------------------------------------------

// §12.6: pattern as constant expression in case-matches
TEST(ParserA60701, PatternConstantExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) matches\n"
      "      5: y = 8'd10;\n"
      "      10: y = 8'd20;\n"
      "      default: y = 8'd30;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// pattern ::= . variable_identifier
// ---------------------------------------------------------------------------

// §12.6: pattern with identifier binding (.name)
TEST(ParserA60701, PatternDotIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (v matches .n) x = n;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// pattern ::= .*
// ---------------------------------------------------------------------------

// §12.6: wildcard pattern .*
TEST(ParserA60701, PatternWildcard) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (v matches .*) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// pattern ::= tagged member_identifier [ pattern ]
// ---------------------------------------------------------------------------

// §12.6: tagged union pattern
TEST(ParserA60701, PatternTagged) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(v) matches\n"
      "      tagged Valid .n: x = n;\n"
      "      tagged Invalid: x = 0;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §12.6: tagged pattern with nested assignment pattern
TEST(ParserA60701, PatternTaggedWithAssignmentPattern) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(instr) matches\n"
      "      tagged Add '{.r1, .r2, .rd}: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §12.6: tagged pattern with parenthesized nested tagged pattern
TEST(ParserA60701, PatternTaggedNested) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(instr) matches\n"
      "      tagged Jmp (tagged JmpU .a): pc = a;\n"
      "      default: pc = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §12.6: tagged void member (no nested pattern)
TEST(ParserA60701, PatternTaggedVoidMember) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(v) matches\n"
      "      tagged Invalid: x = 0;\n"
      "      default: x = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
}

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
// pattern ::= '{ member_identifier : pattern { , member_identifier : pattern } }
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
// assignment_pattern ::= '{ constant_expression { expression { , expression } } }
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
//   ps_type_identifier | ps_parameter_identifier | integer_atom_type | type_reference
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
// assignment_pattern_variable_lvalue ::= '{ variable_lvalue { , variable_lvalue } }
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
  auto *stmt = FirstInitialStmt(r);
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
  auto *stmt = FirstInitialStmt(r);
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
  auto *stmt = FirstInitialStmt(r);
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
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  auto *rhs = stmt->rhs;
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
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
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
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(rhs->elements.size(), 1u);
  // The replication element is a kReplicate expression
  auto *rep = rhs->elements[0];
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
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
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
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements.size(), 0u);
}

// =============================================================================
// A.6.7.1 Patterns — Elaboration tests
// =============================================================================

// §10.9: positional assignment pattern elaborates for struct init
TEST(ElabA60701, StructPositionalPatternElaborates) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = '{8'd10, 8'd20};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// §10.9: named assignment pattern elaborates for struct init
TEST(ElabA60701, StructNamedPatternElaborates) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{a: 8'd1, b: 8'd2};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// §10.9: assignment pattern with default key elaborates
TEST(ElabA60701, PatternDefaultKeyElaborates) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [0:3];\n"
      "  initial begin\n"
      "    arr = '{default: 8'd0};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// §10.9: typed assignment pattern expression elaborates
TEST(ElabA60701, TypedPatternExpressionElaborates) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] x; logic [7:0] y; } coord_t;\n"
      "  coord_t c;\n"
      "  initial begin\n"
      "    c = coord_t'{x: 8'd5, y: 8'd10};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// §12.6: case-matches statement elaborates
TEST(ElabA60701, CaseMatchesElaborates) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    case(x) matches\n"
      "      8'd5: y = 8'd10;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// §12.6.2: matches operator in if-condition elaborates
TEST(ElabA60701, MatchesInIfElaborates) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd3;\n"
      "    if (x matches 8'd3) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// =============================================================================
// A.6.7.1 Patterns — Simulation tests
// =============================================================================

// ---------------------------------------------------------------------------
// assignment_pattern: positional — simulation
// ---------------------------------------------------------------------------

// §10.9: positional assignment pattern packs elements MSB-first
TEST(SimA60701, PositionalPatternPacksMSBFirst) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    x = '{8'd1, 8'd2};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // '{8'd1, 8'd2} = {8'h01, 8'h02} = 16'h0102 = 258
  EXPECT_EQ(var->value.ToUint64(), 258u);
}

// §10.9: single-element positional pattern
TEST(SimA60701, SingleElementPositionalPattern) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = '{8'd42};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// §10.9: four-element positional pattern
TEST(SimA60701, FourElementPositionalPattern) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    x = '{8'd1, 8'd2, 8'd3, 8'd4};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // '{8'd1, 8'd2, 8'd3, 8'd4} = 32'h01020304 = 16909060
  EXPECT_EQ(var->value.ToUint64(), 0x01020304u);
}

// ---------------------------------------------------------------------------
// assignment_pattern: named struct — simulation
// ---------------------------------------------------------------------------

// §10.9.2: named assignment pattern for struct initialization
TEST(SimA60701, NamedStructPatternInit) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{a: 8'd10, b: 8'd20};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);
  // a=10 in upper byte, b=20 in lower byte: (10 << 8) | 20 = 2580
  EXPECT_EQ(var->value.ToUint64(), 2580u);
}

// §10.9.2: named pattern with reversed field order
TEST(SimA60701, NamedStructPatternReversedOrder) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{b: 8'd20, a: 8'd10};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);
  // Same result as above regardless of key order: (10 << 8) | 20 = 2580
  EXPECT_EQ(var->value.ToUint64(), 2580u);
}

// §10.9.2: named pattern with default key fills remaining fields
TEST(SimA60701, NamedStructPatternWithDefault) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{a: 8'd10, default: 8'd99};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);
  // a=10 (explicit), b=99 (default): (10 << 8) | 99 = 2659
  EXPECT_EQ(var->value.ToUint64(), 2659u);
}

// §10.9.2: named pattern with only default key
TEST(SimA60701, NamedStructPatternOnlyDefault) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{default: 8'd55};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);
  // Both a=55, b=55: (55 << 8) | 55 = 14135
  EXPECT_EQ(var->value.ToUint64(), 14135u);
}

// ---------------------------------------------------------------------------
// assignment_pattern: positional struct — simulation
// ---------------------------------------------------------------------------

// §10.9: positional assignment pattern for struct
TEST(SimA60701, PositionalStructPatternInit) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = '{8'd3, 8'd7};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);
  // a=3 in upper byte, b=7 in lower byte: (3 << 8) | 7 = 775
  EXPECT_EQ(var->value.ToUint64(), 775u);
}

// ---------------------------------------------------------------------------
// assignment_pattern: struct with three fields — simulation
// ---------------------------------------------------------------------------

// §10.9.2: struct with three fields, named pattern
TEST(SimA60701, ThreeFieldStructNamedPattern) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] x;\n"
      "    logic [7:0] y;\n"
      "    logic [7:0] z;\n"
      "  } triple_t;\n"
      "  triple_t v;\n"
      "  initial begin\n"
      "    v = triple_t'{x: 8'd1, y: 8'd2, z: 8'd3};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("v");
  ASSERT_NE(var, nullptr);
  // x=1 bits[23:16], y=2 bits[15:8], z=3 bits[7:0]: 0x010203 = 66051
  EXPECT_EQ(var->value.ToUint64(), 0x010203u);
}

// ---------------------------------------------------------------------------
// case-matches: constant pattern — simulation
// ---------------------------------------------------------------------------

// §12.6.1: case-matches selects matching constant pattern
TEST(SimA60701, CaseMatchesConstantMatch) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd2;\n"
      "    case(sel) matches\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd2: x = 8'd20;\n"
      "      8'd3: x = 8'd30;\n"
      "      default: x = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// §12.6.1: case-matches falls through to default
TEST(SimA60701, CaseMatchesDefaultFallthrough) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd99;\n"
      "    case(sel) matches\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd2: x = 8'd20;\n"
      "      default: x = 8'd77;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

// §12.6.1: case-matches first match wins
TEST(SimA60701, CaseMatchesFirstMatchWins) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd1;\n"
      "    case(sel) matches\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "      default: x = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// ---------------------------------------------------------------------------
// matches operator in if-condition — simulation
// ---------------------------------------------------------------------------

// §12.6.2: matches with constant pattern — true case
TEST(SimA60701, MatchesConstantTrue) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    if (x matches 8'd5) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §12.6.2: matches with constant pattern — false case
TEST(SimA60701, MatchesConstantFalse) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    if (x matches 8'd10) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// ---------------------------------------------------------------------------
// assignment_pattern in procedural assignment — simulation
// ---------------------------------------------------------------------------

// §10.9: assignment pattern in blocking assignment
TEST(SimA60701, PatternInBlockingAssignment) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    b = 8'd0;\n"
      "    a = 8'd11;\n"
      "    b = 8'd22;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *a = f.ctx.FindVariable("a");
  auto *b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 11u);
  EXPECT_EQ(b->value.ToUint64(), 22u);
}

// §10.9: assignment pattern used in conditional branch
TEST(SimA60701, PatternInConditionalBranch) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    if (1) x = '{8'd5, 8'd6};\n"
      "    else x = '{8'd0, 8'd0};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // '{8'd5, 8'd6} = {8'h05, 8'h06} = 16'h0506 = 1286
  EXPECT_EQ(var->value.ToUint64(), 1286u);
}

// §10.9: assignment pattern used in case item body
TEST(SimA60701, PatternInCaseItemBody) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    sel = 8'd1;\n"
      "    case(sel)\n"
      "      8'd0: x = '{8'd0, 8'd0};\n"
      "      8'd1: x = '{8'd10, 8'd20};\n"
      "      default: x = '{8'd0, 8'd0};\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // '{8'd10, 8'd20} = {8'h0A, 8'h14} = 16'h0A14 = 2580
  EXPECT_EQ(var->value.ToUint64(), 2580u);
}

// §10.9: assignment pattern in for loop body
TEST(SimA60701, PatternInForLoop) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    x = 16'd0;\n"
      "    for (int i = 0; i < 3; i = i + 1) begin\n"
      "      x = '{8'd7, 8'd8};\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // '{8'd7, 8'd8} = {8'h07, 8'h08} = 16'h0708 = 1800
  EXPECT_EQ(var->value.ToUint64(), 1800u);
}

// ---------------------------------------------------------------------------
// constant_assignment_pattern_expression — simulation
// ---------------------------------------------------------------------------

// §10.9: constant assignment pattern in variable declaration initializer
TEST(SimA60701, ConstPatternInVarDeclInit) {
  SimA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p = '{8'd100, 8'd200};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("p");
  ASSERT_NE(var, nullptr);
  // '{8'd100, 8'd200} = {8'h64, 8'hC8} = 16'h64C8 = 25800
  EXPECT_EQ(var->value.ToUint64(), 25800u);
}
