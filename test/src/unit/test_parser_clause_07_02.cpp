// §7.2: Structures

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA221, StructMemberRandc) {
  // random_qualifier: randc
  auto r = Parse(
      "module m;\n"
      "  struct { randc bit [7:0] x; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& members = r.cu->modules[0]->items[0]->data_type.struct_members;
  ASSERT_GE(members.size(), 1u);
  EXPECT_TRUE(members[0].is_randc);
}

// --- struct_union_member ---
// {attribute_instance} [random_qualifier] data_type_or_void
//   list_of_variable_decl_assignments ;
TEST(ParserA221, StructMemberBasic) {
  auto r = Parse(
      "module m;\n"
      "  struct { logic [7:0] data; int count; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& members = r.cu->modules[0]->items[0]->data_type.struct_members;
  EXPECT_EQ(members.size(), 2u);
  EXPECT_EQ(members[0].name, "data");
  EXPECT_EQ(members[1].name, "count");
}

TEST(ParserA221, StructMemberRand) {
  // random_qualifier: rand
  auto r = Parse(
      "module m;\n"
      "  struct { rand int a; int b; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& members = r.cu->modules[0]->items[0]->data_type.struct_members;
  ASSERT_GE(members.size(), 2u);
  EXPECT_TRUE(members[0].is_rand);
  EXPECT_FALSE(members[1].is_rand);
}

TEST(ParserA221, StructMemberAttr) {
  // {attribute_instance} before struct member
  auto r = Parse(
      "module m;\n"
      "  struct { (* mark *) int a; int b; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& members = r.cu->modules[0]->items[0]->data_type.struct_members;
  ASSERT_GE(members.size(), 2u);
  EXPECT_FALSE(members[0].attrs.empty());
  EXPECT_TRUE(members[1].attrs.empty());
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

}  // namespace
