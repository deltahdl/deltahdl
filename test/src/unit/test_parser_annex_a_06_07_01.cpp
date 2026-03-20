#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(PatternParsing, AssignmentPatternExprList) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = '{1, 2, 3};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(PatternParsing, AssignmentPatternStructKeys) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = '{x: 1, y: 2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, AssignmentPatternReplication) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = '{4{0}};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, AssignmentPatternDefault) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = '{default: 0};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, AssignmentPatternWithType) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { int x; int y; } point_t;\n"
      "  initial begin\n"
      "    point_t p = point_t'{x: 1, y: 2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, AssignmentPatternIntegerAtomType) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int a = int'{1};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, AssignmentPatternNetLvalue) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign '{a, b} = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, AssignmentPatternVariableLvalue) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    '{a, b} = '{1, 2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, CaseMatchesPattern) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (x) matches\n"
      "      .a: $display(\"a\");\n"
      "      .b: $display(\"b\");\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}


TEST(AssignmentPatternParsing, TypePrefixedPattern) {
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
TEST(AssignmentPatternParsing, AssignmentPatternTypePrefixed) {
  auto r = Parse(
      "module m;\n"
      "  typedef int T[3];\n"
      "  T a = T'{1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(PatternParsing, AssignmentPatternWithTypeSizedFields) {
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

TEST(PatternParsing, AssignmentPatternWithIntegerAtomType) {
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

TEST(PatternParsing, PatternKeyDefault) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{default: 0};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, AssignmentPatternVariableLvalueThreeElements) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    '{a, b, c} = '{1, 2, 3};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, AssignmentPatternElementsCount) {
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

TEST(AssignmentPatternParsing, AssignmentPatternPositionalElements) {
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

TEST(PatternParsing, EmptyAssignmentPattern) {
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


TEST(AssignmentPatternParsing, AssignmentPatternInArrayDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int arr [3] = '{0, 1, 2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, PositionalAssignmentPatternBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{1, 2, 3};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, AssignmentPatternReplicationSizedLiteral) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{4{8'd0}};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, AssignmentPatternReplicationMultiElem) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{2{a, b}};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, ArrayPatternKeyConstExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{0: 8'd1, 1: 8'd2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, ReplicationPatternRepeatCount) {
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

  auto* rep = rhs->elements[0];
  EXPECT_EQ(rep->kind, ExprKind::kReplicate);
  EXPECT_NE(rep->repeat_count, nullptr);
}

TEST(AssignmentPatternParsing, AssignmentPatternPositionalParse) {
  auto r = Parse(
      "module t;\n"
      "  initial x = '{1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
}

TEST(AssignmentPatternParsing, AssignmentPatternInConstArrayDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int arr [3] = '{1, 2, 3};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssignmentPatternParsing, AssignmentPatternExpression) {
  auto r = Parse(
      "module t;\n"
      "  int arr[3];\n"
      "  initial arr = '{1, 2, 3};\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements.size(), 3u);
}

TEST(AssignmentPatternParsing, AssignmentPatternPositional) {
  auto r = Parse(
      "module t;\n"
      "  int C[3] = '{10, 20, 30};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->init_expr, nullptr);
  EXPECT_EQ(item->init_expr->kind, ExprKind::kAssignmentPattern);
}

TEST(AssignmentPatternParsing, AssignmentPatternIntKey) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef int triple[1:3];\n"
              "  triple t = '{1:1, default:0};\n"
              "endmodule"));
}

TEST(AssignmentPatternParsing, AssignmentPatternArrayReplication) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int a[1:3] = '{3{1}};\n"
              "endmodule"));
}

TEST(AssignmentPatternParsing, NestedAssignmentPatterns) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; shortreal b;} ab;\n"
              "  ab abarr[1:0] = '{'{1, 1.0}, '{2, 2.0}};\n"
              "endmodule"));
}

TEST(ArrayAssignmentPatterns, NestedStructPatternElements) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct {int a; int b;} ab;\n"
      "  ab arr[1:0];\n"
      "  initial arr = '{'{1, 2}, '{3, 4}};\n"
      "endmodule\n");
  VerifyNestedPatternElements(r, 2u);
}

TEST(NestedReplication, NestedReplication) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; int b[4];} ab_t;\n"
              "  int a, b, c;\n"
              "  ab_t v1[1:0] [2:0];\n"
              "  initial v1 = '{2{'{3{'{a,'{2{b,c}}}}}}};\n"
              "endmodule\n"));
}

TEST(EmptyAssignmentPattern, EmptyAssignmentPattern) {
  auto r = Parse(
      "module m;\n"
      "  initial x = '{};\n"
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

TEST(AssignmentPatternReplication, NestedStructReplication) {
  EXPECT_TRUE(
      ParseOk("module top();\n"
              "  struct {int X,Y,Z;} XYZ = '{3{1}};\n"
              "  typedef struct {int a,b[4];} ab_t;\n"
              "  int a,b,c;\n"
              "  initial begin\n"
              "    ab_t v1[1:0] [2:0];\n"
              "    v1 = '{2{'{3{'{a,'{2{b,c}}}}}}};\n"
              "  end\n"
              "endmodule\n"));
}

TEST(AssignmentPatternDefault, AssignmentPatternDefault) {
  auto r = Parse(
      "module t;\n"
      "  initial x = '{default: 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  std::string expected_keys[] = {"default"};
  VerifyPatternKeys(rhs, expected_keys, std::size(expected_keys));
}


TEST(AssignmentPatternParsing, ArrayOfStructsPattern) {
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

TEST(PatternParsing, PatternAssignmentNamed) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{a: 1, b: 2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssignmentPatternParsing, AssignmentPatternStruct) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { int x; int y; } point_t;\n"
      "  point_t p = '{x: 1, y: 2};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 2u);
}

TEST(AssignmentPatternParsing, PackedStructAssignmentPattern) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] opcode;\n"
      "    logic [7:0] data;\n"
      "  } cmd_t;\n"
      "  cmd_t c;\n"
      "  initial c = '{8'h01, 8'hFF};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
}

TEST(AssignmentPatternParsing, AssignmentPatternInForLoop) {
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

TEST(PatternParsing, StructurePatternKeyMemberAndDefault) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{a: 5, default: 0};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssignmentPatternParsing, PositionalPatternElements) {
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

TEST(AssignmentPatternParsing, NamedPatternKeysThreeMembers) {
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

TEST(AssignmentPatternParsing, MultipleVarsWithPatternInit) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; int b; } pair_t;\n"
              "  pair_t p1 = '{1, 2};\n"
              "  pair_t p2 = '{3, 4};\n"
              "  pair_t p3 = '{default: 0};\n"
              "endmodule\n"));
}

TEST(PatternParsing, AssignmentPatternKeysPopulated) {
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

TEST(AssignmentPatternParsing, StructAssignmentPattern) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; } pair;\n"
      "  initial begin\n"
      "    pair p = '{1, 2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  ASSERT_NE(stmt->var_init, nullptr);
  EXPECT_EQ(stmt->var_init->kind, ExprKind::kAssignmentPattern);
}

TEST(AssignmentPatternParsing, NamedAssignmentPattern) {
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

TEST(AssignmentPatternParsing, DefaultAssignmentPattern) {
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

TEST(AssignmentPatternParsing, NamedWithDefault) {
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

TEST(AssignmentPatternParsing, ReplicationPattern) {
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

TEST(AssignmentPatternParsing, AssignmentPatternInInitialBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; int b; } s_t;\n"
              "  s_t s;\n"
              "  initial begin\n"
              "    s = '{10, 20};\n"
              "  end\n"
              "endmodule\n"));
}

TEST(StructAssignmentPatterns, NestedStructPattern) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int x; int y; } point_t;\n"
      "  typedef struct { point_t origin; point_t size; } rect_t;\n"
      "  rect_t r1;\n"
      "  initial r1 = '{'{0, 0}, '{10, 20}};\n"
      "endmodule\n");
  VerifyNestedPatternElements(r, 2u);
}

TEST(AssignmentPatternParsing, AssignmentPatternNamed) {
  auto r = Parse(
      "module t;\n"
      "  initial x = '{a: 0, b: 1};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements.size(), 2u);
  std::string expected_keys[] = {"a", "b"};
  VerifyPatternKeys(rhs, expected_keys, std::size(expected_keys));
}

TEST(AssignmentPatternParsing, AssignmentPatternTypeKey) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { int x; int y; } ms_t;\n"
              "  ms_t ms = '{int:0, int:1};\n"
              "endmodule"));
}

TEST(AssignmentPatternParsing, AssignmentPatternDefaultKey) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { int x; int y; } ms_t;\n"
              "  ms_t ms = '{default:1};\n"
              "endmodule"));
}

TEST(AssignmentPatternParsing, StructPositionalAssignmentPattern) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; shortreal b;} ab;\n"
              "  ab c;\n"
              "  initial c = '{0, 0.0};\n"
              "endmodule"));
}

TEST(AssignmentPatternParsing, StructNamedAssignmentPattern) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; shortreal b;} ab;\n"
              "  ab c;\n"
              "  initial c = '{a:0, b:0.0};\n"
              "endmodule"));
}

TEST(PositionalStructAssignmentPattern, PositionalStructPattern) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct {int a; shortreal b;} ab;\n"
      "  ab c;\n"
      "  initial c = '{0, 0.0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
  EXPECT_TRUE(stmt->rhs->pattern_keys.empty());
}

TEST(StructureAssignmentPatternMemberKey, MemberNameAndValue) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct {int a; shortreal b;} ab;\n"
      "  ab c;\n"
      "  initial c = '{a:0, b:0.0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(stmt->rhs->pattern_keys.size(), 2u);
  EXPECT_EQ(stmt->rhs->pattern_keys[0], "a");
  EXPECT_EQ(stmt->rhs->pattern_keys[1], "b");
}

TEST(StructureAssignmentPatternDefault, DefaultValue) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct {int a; int b;} ab;\n"
      "  ab c;\n"
      "  initial c = '{default:0};\n"
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

TEST(TypePrefixedPattern, TypePrefixedPattern) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; shortreal b;} ab;\n"
              "  ab d;\n"
              "  initial d = ab'{int:1, shortreal:1.0};\n"
              "endmodule\n"));
}

TEST(ReplicationPattern, ReplicationPattern) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct {int X; int Y; int Z;} xyz_t;\n"
      "  xyz_t s;\n"
      "  initial s = '{3{1}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
}

TEST(StructAssignmentPattern, StructPatternInVarDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; int b;} ab;\n"
              "  ab c = '{0, 1};\n"
              "endmodule\n"));
}

TEST(StructureAssignmentPatternDefault, MemberNameWithDefault) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct {int a; int b; int c;} s_t;\n"
      "  s_t s;\n"
      "  initial s = '{a: 5, default: 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->pattern_keys.size(), 2u);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
}

TEST(PatternParsing, PatternConstantExpr) {
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

TEST(PatternParsing, PatternTagged) {
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

TEST(PatternParsing, PatternTaggedWithAssignmentPattern) {
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

TEST(PatternParsing, PatternTaggedNested) {
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

TEST(PatternParsing, PatternTaggedVoidMember) {
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
}

TEST(PatternParsing, PatternAssignmentWithDotBindings) {
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

TEST(PatternParsing, PatternDotIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (v matches .n) x = n;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, PatternWildcard) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (v matches .*) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, PatternGuardExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (v matches .n &&& (n > 0)) x = n;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, ConstantAssignmentPatternExpression) {
  auto r = Parse(
      "module m;\n"
      "  localparam int arr [3] = '{1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, AssignmentPatternVariableLvalueWithIndex) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    '{a[0], b[1]} = '{1, 2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, PatternDotBindingInIfMatches) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (s matches '{.a, .b}) x = a + b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssignmentPatternParsing, AssignmentPatternNetLvalueThreeElements) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c;\n"
      "  assign '{a, b, c} = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssignmentPatternParsing, TypeReferencePatternExpression) {
  auto r = Parse(
      "module m;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    x = type(x)'{8'd1, 8'd2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- Error conditions ---

TEST(PatternParsing, ErrorAssignmentPatternMissingCloseBrace) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{1, 2, 3;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PatternParsing, ErrorAssignmentPatternMissingApostrophe) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = {1, 2, 3};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_NE(rhs->kind, ExprKind::kAssignmentPattern);
}

TEST(PatternParsing, ErrorReplicationMissingCloseBrace) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{3{8'd5};\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
