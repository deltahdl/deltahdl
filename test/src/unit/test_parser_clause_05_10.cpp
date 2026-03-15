#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(LexicalConventionParsing, StructLiteralExprKind) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { int a; int b; } ab_t;\n"
      "  ab_t s;\n"
      "  initial s = '{0, 1};\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements.size(), 2u);
}

TEST(LexicalConventionParsing, NestedBracesParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; shortreal b; } ab;\n"
              "  ab abarr [1:0];\n"
              "  initial abarr = '{'{1, 1.0}, '{2, 2.0}};\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, NestedBracesExprKind) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { int a; int b; } ab_t;\n"
      "  ab_t arr [0:1];\n"
      "  initial arr = '{'{1, 2}, '{3, 4}};\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(rhs->elements.size(), 2u);
  EXPECT_EQ(rhs->elements[0]->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements[1]->kind, ExprKind::kAssignmentPattern);
}

TEST(LexicalConventionParsing, TypePrefixedStructLiteralParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; shortreal b; } ab;\n"
              "  ab c;\n"
              "  initial c = ab'{0, 0.0};\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, ReplicationInStructLiteralParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int x; int y; int z; } xyz_t;\n"
              "  xyz_t s;\n"
              "  initial s = '{3{1}};\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, StructureLiteralParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; int b; } ab_t;\n"
              "  ab_t s;\n"
              "  initial s = '{0, 1};\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, StructureLiteralWithNamedMembersParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; int b; } ab_t;\n"
              "  ab_t s;\n"
              "  initial s = '{a:0, b:1};\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, StructureLiteralWithDefaultParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct { int a; int b; } ab_t;\n"
              "  ab_t s;\n"
              "  initial s = '{default:0};\n"
              "endmodule\n"));
}

}  // namespace
