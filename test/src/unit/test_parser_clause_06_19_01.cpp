// §6.19.1: Defining new data types as enumerated types

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserAnnexA, A2TypedefEnumWithBase) {
  auto r = Parse("module m;\n"
                 "  typedef enum logic [1:0] {IDLE, RUN, DONE} state_t;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kTypedef);
}

TEST(ParserA213, TypedefEnum) {
  auto r = Parse("module m; typedef enum {A, B, C} abc_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kEnum);
}
// Typedef enum used as a named type for variable declarations.
TEST(ParserSection8, EnumTypedefUsage) {
  auto r = Parse("module m;\n"
                 "  typedef enum {NO, YES} boolean;\n"
                 "  boolean flag;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto &items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(items[0]->name, "boolean");
  EXPECT_EQ(items[0]->typedef_type.enum_members.size(), 2u);
  EXPECT_EQ(items[1]->name, "flag");
}
TEST(Parser, EnumWithValues) {
  auto r = Parse("module t;\n"
                 "  typedef enum { IDLE=0, RUN=1, STOP=2 } cmd_t;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto &members = r.cu->modules[0]->items[0]->typedef_type.enum_members;
  std::string expected[] = {"IDLE", "RUN", "STOP"};
  ASSERT_EQ(members.size(), std::size(expected));
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(members[i].name, expected[i]) << "member " << i;
    EXPECT_NE(members[i].value, nullptr) << "member " << i;
  }
}

// 23. Enum in module scope
TEST(ParserClause03, Cl3_13_EnumInModuleScope) {
  auto r = Parse("module m;\n"
                 "  typedef enum logic [1:0] {IDLE, RUN, DONE} state_t;\n"
                 "  state_t current_state;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *mod = r.cu->modules[0];
  bool found_typedef = false;
  for (auto *item : mod->items) {
    if (item->kind == ModuleItemKind::kTypedef) {
      found_typedef = true;
      EXPECT_EQ(item->typedef_type.enum_members.size(), 3u);
    }
  }
  EXPECT_TRUE(found_typedef);
}
// Typedef of enum with named type for reuse.
TEST(ParserSection8, TypedefEnumWithMembers) {
  auto r = Parse("module m;\n"
                 "  typedef enum {RED, GREEN, BLUE} color_t;\n"
                 "  color_t c;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto &items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(items[0]->typedef_type.kind, DataTypeKind::kEnum);
}
// =========================================================================
// §6.19: Enumerations
// =========================================================================
TEST(ParserSection6, EnumBasic) {
  auto r = Parse("module t;\n"
                 "  typedef enum { RED, GREEN, BLUE } color_t;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kEnum);
  EXPECT_EQ(item->typedef_type.enum_members.size(), 3u);
}

} // namespace
