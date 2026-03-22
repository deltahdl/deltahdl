#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(StructDeclarationParsing, StructMemberRandc) {
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

TEST(StructDeclarationParsing, StructMemberBasic) {
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

TEST(StructDeclarationParsing, StructMemberRand) {
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

TEST(StructDeclarationParsing, StructMemberAttr) {
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

TEST(StructDeclarationParsing, MemberAccessOnRHS) {
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
TEST(StructDeclarationParsing, InlineStructVar) {
  auto r = Parse(
      "module t;\n"
      "  struct { int x; int y; } point;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "point");
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kStruct);
  ASSERT_EQ(item->data_type.struct_members.size(), 2);
}
static void VerifyStructMemberNames(const std::vector<StructMember>& members,
                                    const std::string expected_names[],
                                    size_t count) {
  ASSERT_EQ(members.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(members[i].name, expected_names[i]) << "member " << i;
  }
}

TEST(StructDeclarationParsing, StructBasic) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct {\n"
      "    int a;\n"
      "    logic [7:0] b;\n"
      "  } my_struct;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kStruct);
  std::string expected_names[] = {"a", "b"};
  VerifyStructMemberNames(item->typedef_type.struct_members, expected_names,
                          std::size(expected_names));
}

TEST(StructDeclarationParsing, StructMemberUnpackedDim) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct {\n"
      "    byte data[4];\n"
      "  } packet;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 1u);
  EXPECT_FALSE(item->typedef_type.struct_members[0].unpacked_dims.empty());
}

TEST(StructDeclarationParsing, StructMultipleMembersSameType) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct {\n"
      "    int x, y, z;\n"
      "  } point;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  std::string expected_names[] = {"x", "y", "z"};
  ASSERT_EQ(item->typedef_type.struct_members.size(),
            std::size(expected_names));
  for (size_t i = 0; i < std::size(expected_names); ++i) {
    EXPECT_EQ(item->typedef_type.struct_members[i].name, expected_names[i])
        << "member " << i;
  }
}

TEST(StructDeclarationParsing, UnpackedStructDecl) {
  auto r = Parse(
      "module t;\n"
      "  struct {\n"
      "    int x;\n"
      "    real y;\n"
      "    string s;\n"
      "  } my_unpacked;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kStruct);
  EXPECT_FALSE(item->data_type.is_packed);
  EXPECT_EQ(item->data_type.struct_members.size(), 3u);
}

TEST(StructDeclarationParsing, UnpackedStructTypedefDecl) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct {\n"
      "    int addr;\n"
      "    int crc;\n"
      "    byte data [4];\n"
      "  } packet;\n"
      "  packet p;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_FALSE(item->typedef_type.is_packed);
}

TEST(StructDeclarationParsing, VoidMemberParsed) {
  auto r = Parse(
      "module m;\n"
      "  struct { void v; int a; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& members = r.cu->modules[0]->items[0]->data_type.struct_members;
  ASSERT_GE(members.size(), 2u);
  EXPECT_EQ(members[0].type_kind, DataTypeKind::kVoid);
  EXPECT_EQ(members[0].name, "v");
}

TEST(StructDeclarationParsing, NestedInlineStructMember) {
  auto r = Parse(
      "module m;\n"
      "  struct {\n"
      "    struct { int x; int y; } point;\n"
      "    int id;\n"
      "  } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& members = r.cu->modules[0]->items[0]->data_type.struct_members;
  ASSERT_GE(members.size(), 2u);
  EXPECT_EQ(members[0].type_kind, DataTypeKind::kStruct);
  EXPECT_EQ(members[0].name, "point");
  EXPECT_EQ(members[1].name, "id");
}

}  // namespace
