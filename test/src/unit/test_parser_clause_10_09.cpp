// §10.9: Assignment patterns

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// 20. Struct with type-prefixed assignment pattern T'{...}.
TEST(ParserSection7, Sec7_2_2_TypePrefixedPattern) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial p = pair_t'{100, 200};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

struct ParseResult10b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult10b Parse(const std::string& src) {
  ParseResult10b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

TEST(ParserSection10, AssignmentPatternTypePrefixed) {
  auto r = Parse(
      "module m;\n"
      "  typedef int T[3];\n"
      "  T a = T'{1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
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

// --- §5.12 Attributes ---
struct ParseResult512 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult512 Parse(const std::string& src) {
  ParseResult512 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult512& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
}

TEST(ParserCh510, AssignmentPatternPositional_Elements) {
  auto r = Parse(
      "module t;\n"
      "  initial x = '{1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->elements.size(), 3u);
  EXPECT_TRUE(rhs->pattern_keys.empty());
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

}  // namespace
