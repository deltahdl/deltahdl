#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult7e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult7e Parse(const std::string& src) {
  ParseResult7e result;
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

static ModuleItem* FirstItem(ParseResult7e& r) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.empty())
    return nullptr;
  return r.cu->modules[0]->items[0];
}

static ModuleItem* NthItem(ParseResult7e& r, size_t n) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.size() <= n)
    return nullptr;
  return r.cu->modules[0]->items[n];
}

static Stmt* FirstInitialStmt(ParseResult7e& r) {
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

static Stmt* NthInitialStmt(ParseResult7e& r, size_t n) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        if (item->body->stmts.size() > n) return item->body->stmts[n];
      }
      if (n == 0) return item->body;
    }
  }
  return nullptr;
}

// =============================================================================
// LRM section 7.2.2 -- Assigning to structures
// =============================================================================

// 1. Named assignment pattern '{a: 1, b: 2}.
TEST(ParserSection7, Sec7_2_2_NamedAssignmentPattern) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial p = '{a: 10, b: 20};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
  ASSERT_EQ(stmt->rhs->pattern_keys.size(), 2u);
  EXPECT_EQ(stmt->rhs->pattern_keys[0], "a");
  EXPECT_EQ(stmt->rhs->pattern_keys[1], "b");
}

// 2. Default assignment pattern '{default: 0}.
TEST(ParserSection7, Sec7_2_2_DefaultAssignmentPattern) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; int c; } triple_t;\n"
      "  triple_t t1;\n"
      "  initial t1 = '{default: 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_GE(stmt->rhs->pattern_keys.size(), 1u);
  EXPECT_EQ(stmt->rhs->pattern_keys[0], "default");
}

// 3. Named with default pattern '{a: 1, default: 0}.
TEST(ParserSection7, Sec7_2_2_NamedWithDefault) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; int c; } s_t;\n"
      "  s_t s;\n"
      "  initial s = '{a: 1, default: 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
  EXPECT_EQ(stmt->rhs->pattern_keys.size(), 2u);
}

// 4. Assignment pattern with replication '{4{8'h00}}.
TEST(ParserSection7, Sec7_2_2_ReplicationPattern) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { byte a; byte b; byte c; byte d; } quad_t;\n"
      "  quad_t q;\n"
      "  initial q = '{4{8'h00}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
}

// 5. Struct variable assigned from another struct variable.
TEST(ParserSection7, Sec7_2_2_AssignFromStructVar) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int x; int y; } point_t;\n"
      "  point_t a, b;\n"
      "  initial begin\n"
      "    a = '{1, 2};\n"
      "    b = a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = NthInitialStmt(r, 1);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->rhs->text, "a");
}

// 6. Struct member assigned individually (s.a = 1).
TEST(ParserSection7, Sec7_2_2_MemberAssignment) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p.a = 10;\n"
      "    p.b = 20;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = NthInitialStmt(r, 0);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

// 7. Packed struct assigned from integer literal.
TEST(ParserSection7, Sec7_2_2_PackedStructFromInteger) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } word_t;\n"
      "  word_t w;\n"
      "  initial w = 16'hABCD;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kIntegerLiteral);
}

// 8. Packed struct assigned from concatenation.
TEST(ParserSection7, Sec7_2_2_PackedStructFromConcat) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t w;\n"
      "  initial w = {8'hAB, 8'hCD};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
}

// 9. Default member values in struct typedef.
TEST(ParserSection7, Sec7_2_2_DefaultMemberValues) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct {\n"
      "    int addr = 32'h0;\n"
      "    int data = 32'hFF;\n"
      "    bit valid = 1'b0;\n"
      "  } pkt_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 3u);
  EXPECT_NE(item->typedef_type.struct_members[0].init_expr, nullptr);
  EXPECT_NE(item->typedef_type.struct_members[1].init_expr, nullptr);
  EXPECT_NE(item->typedef_type.struct_members[2].init_expr, nullptr);
}

// 10. Struct assigned in initial block with begin/end.
TEST(ParserSection7, Sec7_2_2_AssignInInitialBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; int b; } s_t;\n"
              "  s_t s;\n"
              "  initial begin\n"
              "    s = '{10, 20};\n"
              "  end\n"
              "endmodule\n"));
}

// 11. Struct assigned in always_comb block.
TEST(ParserSection7, Sec7_2_2_AssignInAlwaysComb) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { logic a; logic b; } pair_t;\n"
      "  pair_t p;\n"
      "  logic sel;\n"
      "  always_comb begin\n"
      "    if (sel)\n"
      "      p = '{1'b1, 1'b0};\n"
      "    else\n"
      "      p = '{1'b0, 1'b1};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = NthItem(r, 3);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysCombBlock);
}

// 12. Struct assigned via continuous assign statement.
TEST(ParserSection7, Sec7_2_2_ContinuousAssign) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } s_t;\n"
      "  s_t s;\n"
      "  assign s = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = NthItem(r, 2);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kContAssign);
  ASSERT_NE(item->assign_lhs, nullptr);
  ASSERT_NE(item->assign_rhs, nullptr);
}

// 13. Struct as function return value.
TEST(ParserSection7, Sec7_2_2_FunctionReturnStruct) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int x; int y; } point_t;\n"
      "  function point_t make_point;\n"
      "    input int a, b;\n"
      "    make_point = '{a, b};\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = NthItem(r, 1);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
}

// 14. Struct as function argument.
TEST(ParserSection7, Sec7_2_2_FunctionArgStruct) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; int b; } pair_t;\n"
              "  function int sum_pair;\n"
              "    input pair_t p;\n"
              "    sum_pair = p.a + p.b;\n"
              "  endfunction\n"
              "endmodule\n"));
}

// 15. Nested struct assignment pattern.
TEST(ParserSection7, Sec7_2_2_NestedStructPattern) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int x; int y; } point_t;\n"
      "  typedef struct { point_t origin; point_t size; } rect_t;\n"
      "  rect_t r1;\n"
      "  initial r1 = '{'{0, 0}, '{10, 20}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(stmt->rhs->elements.size(), 2u);
  EXPECT_EQ(stmt->rhs->elements[0]->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(stmt->rhs->elements[1]->kind, ExprKind::kAssignmentPattern);
}

// 16. Array of structs with assignment pattern.
TEST(ParserSection7, Sec7_2_2_ArrayOfStructsPattern) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; int b; } pair_t;\n"
              "  pair_t arr[2];\n"
              "  initial begin\n"
              "    arr[0] = '{1, 2};\n"
              "    arr[1] = '{3, 4};\n"
              "  end\n"
              "endmodule\n"));
}

// 17. Struct type cast from integer using type'(expr).
TEST(ParserSection7, Sec7_2_2_TypeCastToStruct) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } s_t;\n"
      "  s_t s;\n"
      "  initial s = s_t'(16'hBEEF);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCast);
}

// 18. Struct comparison with another struct.
TEST(ParserSection7, Sec7_2_2_StructComparison) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  pair_t x, y;\n"
      "  logic eq;\n"
      "  initial eq = (x == y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kEqEq);
}

// 19. Struct member access on RHS.
TEST(ParserSection7, Sec7_2_2_MemberAccessOnRHS) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int x; int y; } point_t;\n"
      "  point_t p;\n"
      "  int val;\n"
      "  initial val = p.x + p.y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
  ASSERT_NE(stmt->rhs->lhs, nullptr);
  EXPECT_EQ(stmt->rhs->lhs->kind, ExprKind::kMemberAccess);
  ASSERT_NE(stmt->rhs->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->rhs->kind, ExprKind::kMemberAccess);
}

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

// 21. Packed struct bitwise operations.
TEST(ParserSection7, Sec7_2_2_PackedStructBitwise) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } w_t;\n"
      "  w_t x, y, z;\n"
      "  initial z = x & y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kAmp);
}

// 22. Struct in conditional expression (ternary).
TEST(ParserSection7, Sec7_2_2_StructTernary) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  pair_t x, y, z;\n"
      "  logic sel;\n"
      "  initial z = sel ? x : y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
}

// 23. Struct variable declaration with initializer in initial block.
TEST(ParserSection7, Sec7_2_2_VarDeclWithInit) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  initial begin\n"
      "    pair_t p = '{5, 10};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->var_name, "p");
  ASSERT_NE(stmt->var_init, nullptr);
  EXPECT_EQ(stmt->var_init->kind, ExprKind::kAssignmentPattern);
}

// 24. Struct assigned in for loop body.
TEST(ParserSection7, Sec7_2_2_AssignInForLoop) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int idx; int val; } entry_t;\n"
              "  entry_t table[4];\n"
              "  initial begin\n"
              "    for (int i = 0; i < 4; i = i + 1) begin\n"
              "      table[i] = '{i, i * 10};\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}

// 25. Struct with packed array member assigned.
TEST(ParserSection7, Sec7_2_2_PackedArrayMemberAssign) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct {\n"
      "    logic [7:0] data;\n"
      "    logic [3:0] tag;\n"
      "  } tagged_data_t;\n"
      "  tagged_data_t td;\n"
      "  initial begin\n"
      "    td.data = 8'hFF;\n"
      "    td.tag = 4'hA;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s1->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s0->lhs->kind, ExprKind::kMemberAccess);
  EXPECT_EQ(s1->lhs->kind, ExprKind::kMemberAccess);
}

// 26. Struct output port assigned in module body.
TEST(ParserSection7, Sec7_2_2_StructOutputPort) {
  EXPECT_TRUE(
      ParseOk("module t(\n"
              "  output logic [15:0] result\n"
              ");\n"
              "  typedef struct packed { logic [7:0] a; logic [7:0] b; } s_t;\n"
              "  s_t s;\n"
              "  assign s = 16'hDEAD;\n"
              "  assign result = s;\n"
              "endmodule\n"));
}

// 27. Positional assignment pattern elements count.
TEST(ParserSection7, Sec7_2_2_PositionalPatternElements) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; int c; } tri_t;\n"
      "  tri_t v;\n"
      "  initial v = '{100, 200, 300};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(stmt->rhs->elements.size(), 3u);
  EXPECT_TRUE(stmt->rhs->pattern_keys.empty());
}

// 28. Packed struct assigned from bit vector and used in expression.
TEST(ParserSection7, Sec7_2_2_PackedStructBitVector) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [3:0] upper;\n"
      "    logic [3:0] lower;\n"
      "  } nibbles_t;\n"
      "  nibbles_t n;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    n = 8'b1010_0101;\n"
      "    result = n;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  ASSERT_NE(s0, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(s0->rhs, nullptr);
  EXPECT_EQ(s0->rhs->kind, ExprKind::kIntegerLiteral);
}

// 29. Named pattern keys verified for three-member struct.
TEST(ParserSection7, Sec7_2_2_NamedPatternKeysThreeMembers) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int x; int y; int z; } vec3_t;\n"
      "  vec3_t v;\n"
      "  initial v = '{x: 1, y: 2, z: 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(stmt->rhs->pattern_keys.size(), 3u);
  EXPECT_EQ(stmt->rhs->pattern_keys[0], "x");
  EXPECT_EQ(stmt->rhs->pattern_keys[1], "y");
  EXPECT_EQ(stmt->rhs->pattern_keys[2], "z");
  ASSERT_EQ(stmt->rhs->elements.size(), 3u);
  EXPECT_EQ(stmt->rhs->elements[0]->kind, ExprKind::kIntegerLiteral);
}

// 30. Multiple struct variables with different initializers.
TEST(ParserSection7, Sec7_2_2_MultipleVarsWithInit) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; int b; } pair_t;\n"
              "  pair_t p1 = '{1, 2};\n"
              "  pair_t p2 = '{3, 4};\n"
              "  pair_t p3 = '{default: 0};\n"
              "endmodule\n"));
}
