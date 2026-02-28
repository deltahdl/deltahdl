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

struct ParseResult7 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult7 Parse(const std::string& src) {
  ParseResult7 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

TEST(Parser, InlineStructVar) {
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

static ModuleItem* FirstItem(ParseResult7& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

static void VerifyStructMemberNames(const std::vector<StructMember>& members,
                                    const std::string expected_names[],
                                    size_t count) {
  ASSERT_EQ(members.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(members[i].name, expected_names[i]) << "member " << i;
  }
}

// =========================================================================
// §7.2: Structures
// =========================================================================
TEST(ParserSection7, StructBasic) {
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

// =========================================================================
// Section 5.6.3: System tasks and system functions
// =========================================================================
struct ParseResult50603 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult50603 Parse(const std::string& src) {
  ParseResult50603 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// --- Comma-separated struct members ---
TEST(ParserCh5, StructMembers_CommaSeparated) {
  auto r = Parse(
      "module m;\n"
      "  struct { int X, Y, Z; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.struct_members.size(), 3u);
}

}  // namespace
