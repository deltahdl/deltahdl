// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserClause05, Cl5_10_MemberNameAndValue) {

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

TEST(ParserClause05, Cl5_10_DefaultValue) {

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

TEST(ParserClause05, Cl5_10_TypePrefixedPattern) {

  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; shortreal b;} ab;\n"
              "  ab d;\n"
              "  initial d = ab'{int:1, shortreal:1.0};\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_10_ReplicationPattern) {

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

TEST(ParserClause05, Cl5_10_StructLiteralInVarDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; int b;} ab;\n"
              "  ab c = '{0, 1};\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_10_MemberNameWithDefault) {
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

TEST(ParserClause05, Cl5_10_NestedReplication) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; int b[4];} ab_t;\n"
              "  int a, b, c;\n"
              "  ab_t v1[1:0] [2:0];\n"
              "  initial v1 = '{2{'{3{'{a,'{2{b,c}}}}}}};\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_10_EmptyAssignmentPattern) {
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

}  // namespace
