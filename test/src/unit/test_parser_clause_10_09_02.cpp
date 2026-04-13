#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(StructPatternParsing, TypePrefixedNamedKeys) {
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

TEST(StructPatternParsing, TypePrefixedPattern) {
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

TEST(StructPatternParsing, TypePrefixedNamedSizedFields) {
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

TEST(StructPatternParsing, NamedKeysModuleScopeDecl) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { int x; int y; } point_t;\n"
      "  point_t p = '{x: 1, y: 2};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 2u);
}

TEST(StructPatternParsing, PackedStructAssignmentPattern) {
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

TEST(StructPatternParsing, AssignmentPatternInForLoop) {
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

TEST(StructPatternParsing, PositionalStructThreeElements) {
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

TEST(StructPatternParsing, NamedPatternKeysThreeMembers) {
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

TEST(StructPatternParsing, MultipleVarsWithPatternInit) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; int b; } pair_t;\n"
              "  pair_t p1 = '{1, 2};\n"
              "  pair_t p2 = '{3, 4};\n"
              "  pair_t p3 = '{default: 0};\n"
              "endmodule\n"));
}

TEST(StructPatternParsing, PositionalLocalVarDecl) {
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

TEST(StructPatternParsing, AssignmentPatternInInitialBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; int b; } s_t;\n"
              "  s_t s;\n"
              "  initial begin\n"
              "    s = '{10, 20};\n"
              "  end\n"
              "endmodule\n"));
}

TEST(StructPatternParsing, NestedStructPattern) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int x; int y; } point_t;\n"
      "  typedef struct { point_t origin; point_t size; } rect_t;\n"
      "  rect_t r1;\n"
      "  initial r1 = '{'{0, 0}, '{10, 20}};\n"
      "endmodule\n");
  VerifyNestedPatternElements(r, 2u);
}

TEST(StructPatternParsing, AssignmentPatternTypeKey) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { int x; int y; } ms_t;\n"
              "  ms_t ms = '{int:0, int:1};\n"
              "endmodule"));
}

TEST(StructPatternParsing, PositionalStructPattern) {
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

TEST(StructPatternParsing, MemberNameAndValue) {
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

TEST(StructPatternParsing, DefaultKeyStructInit) {
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

TEST(StructPatternParsing, TypePrefixedPatternWithTypeKeys) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; shortreal b;} ab;\n"
              "  ab d;\n"
              "  initial d = ab'{int:1, shortreal:1.0};\n"
              "endmodule\n"));
}

TEST(StructPatternParsing, StructPatternInVarDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; int b;} ab;\n"
              "  ab c = '{0, 1};\n"
              "endmodule\n"));
}

TEST(StructPatternParsing, MemberNameWithDefault) {
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

TEST(StructPatternParsing, BitTypeKey) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { bit a; bit b; } s_t;\n"
              "  s_t s;\n"
              "  initial s = '{bit: 1'b0};\n"
              "endmodule\n"));
}

TEST(StructPatternParsing, RegTypeKey) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { reg a; reg b; } s_t;\n"
              "  s_t s;\n"
              "  initial s = '{reg: 1'b0};\n"
              "endmodule\n"));
}

TEST(StructPatternParsing, TimeTypeKey) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { time a; time b; } s_t;\n"
              "  s_t s;\n"
              "  initial s = '{time: 0};\n"
              "endmodule\n"));
}

TEST(StructPatternParsing, RealtimeTypeKey) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { realtime a; realtime b; } s_t;\n"
              "  s_t s;\n"
              "  initial s = '{realtime: 0.0};\n"
              "endmodule\n"));
}

TEST(StructPatternParsing, MemberAndTypeKey) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct {int a; logic [7:0] b;} s_t;\n"
      "  s_t s;\n"
      "  initial s = '{a: 5, logic: 8'd0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(stmt->rhs->pattern_keys.size(), 2u);
  EXPECT_EQ(stmt->rhs->pattern_keys[0], "a");
  EXPECT_EQ(stmt->rhs->pattern_keys[1], "logic");
}

TEST(StructPatternParsing, AllThreeKeyTypes) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct {int a; int b; logic [7:0] c;} s_t;\n"
      "  s_t s;\n"
      "  initial s = '{a: 5, int: 0, default: 8'd99};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(stmt->rhs->pattern_keys.size(), 3u);
  EXPECT_EQ(stmt->rhs->pattern_keys[0], "a");
  EXPECT_EQ(stmt->rhs->pattern_keys[1], "int");
  EXPECT_EQ(stmt->rhs->pattern_keys[2], "default");
}

}  // namespace
