
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

static void VerifyPatternKeys(const Expr* rhs,
                              const std::string expected_keys[], size_t count) {
  ASSERT_EQ(rhs->pattern_keys.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(rhs->pattern_keys[i], expected_keys[i]) << "key " << i;
  }
}

namespace {

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

TEST(ParserSection10, AssignmentPatternStruct) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { int x; int y; } point_t;\n"
      "  point_t p = '{x: 1, y: 2};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 2u);
}

TEST(ParserSection7, Sec7_2_1_PackedAssignFromPattern) {
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

TEST(ParserSection7, Sec7_2_2_MultipleVarsWithInit) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; int b; } pair_t;\n"
              "  pair_t p1 = '{1, 2};\n"
              "  pair_t p2 = '{3, 4};\n"
              "  pair_t p3 = '{default: 0};\n"
              "endmodule\n"));
}

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

TEST(ParserSection7, StructAssignmentPattern) {
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

TEST(StructAssignmentPatterns, NestedStructPattern) {
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

TEST(ParserCh510, AssignmentPatternNamed) {
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

TEST(ParserCh510, AssignmentPattern_TypeKey) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { int x; int y; } ms_t;\n"
              "  ms_t ms = '{int:0, int:1};\n"
              "endmodule"));
}

TEST(ParserCh510, AssignmentPattern_DefaultKey) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { int x; int y; } ms_t;\n"
              "  ms_t ms = '{default:1};\n"
              "endmodule"));
}

TEST(ParserCh510, StructLiteral_Positional) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; shortreal b;} ab;\n"
              "  ab c;\n"
              "  initial c = '{0, 0.0};\n"
              "endmodule"));
}

TEST(ParserCh510, StructLiteral_MemberNameAndValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; shortreal b;} ab;\n"
              "  ab c;\n"
              "  initial c = '{a:0, b:0.0};\n"
              "endmodule"));
}

}
TEST(PositionalStructAssignmentPattern, Cl5_10_PositionalStructLiteral) {
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

TEST(StructureAssignmentPatternMemberKey, Cl5_10_MemberNameAndValue) {
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

TEST(StructureAssignmentPatternDefault, Cl5_10_DefaultValue) {
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

TEST(TypePrefixedPattern, Cl5_10_TypePrefixedPattern) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; shortreal b;} ab;\n"
              "  ab d;\n"
              "  initial d = ab'{int:1, shortreal:1.0};\n"
              "endmodule\n"));
}

TEST(ReplicationPattern, Cl5_10_ReplicationPattern) {
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

TEST(StructAssignmentPattern, Cl5_10_StructLiteralInVarDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; int b;} ab;\n"
              "  ab c = '{0, 1};\n"
              "endmodule\n"));
}

TEST(StructureAssignmentPatternDefault, Cl5_10_MemberNameWithDefault) {
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
}
