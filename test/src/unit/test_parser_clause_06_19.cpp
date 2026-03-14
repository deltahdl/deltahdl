#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast.h"

using namespace delta;

namespace {

TEST(NetAndVariableTypeParsing, EnumBaseAtomType) {
  auto r = Parse("module m; enum int {A, B} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEnum);
}

TEST(NetAndVariableTypeParsing, EnumNameBasic) {
  auto r = Parse("module m; enum {RED, GREEN, BLUE} color; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.enum_members.size(), 3u);
}

TEST(ClassParsing, EnumAnonymousDeclMembers) {
  auto r = Parse(
      "module m;\n"
      "  enum {IDLE, RUNNING, DONE} state;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEnum);
  EXPECT_EQ(item->name, "state");
  ASSERT_EQ(item->data_type.enum_members.size(), 3u);
  EXPECT_EQ(item->data_type.enum_members[0].name, "IDLE");
  EXPECT_EQ(item->data_type.enum_members[1].name, "RUNNING");
  EXPECT_EQ(item->data_type.enum_members[2].name, "DONE");
}

TEST(ClassParsing, EnumExplicitBaseTypeValues) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  enum bit [3:0] {BRONZE = 4'h3, SILVER, GOLD = 4'h5}"
              " medal;\n"
              "endmodule\n"));
}
TEST(Parser, InlineEnumVar) {
  auto r = Parse(
      "module t;\n"
      "  enum { X, Y } my_var;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "my_var");
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEnum);
  ASSERT_EQ(item->data_type.enum_members.size(), 2);
}

TEST(NetAndVariableTypeParsing, DataTypeEnum) {
  auto r = Parse("module m; enum logic [1:0] {A, B, C} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEnum);
}

TEST(NetAndVariableTypeParsing, EnumBaseVectorWithDim) {
  auto r = Parse("module m; enum logic [7:0] {A=0, B=255} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_NE(r.cu->modules[0]->items[0]->data_type.packed_dim_left, nullptr);
}

TEST(NetAndVariableTypeParsing, EnumBaseTypeIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  typedef logic [3:0] nibble_t;\n"
      "  enum nibble_t {A, B} x;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DataTypeParsing, EnumIsIntegral) {
  EXPECT_TRUE(IsIntegralType(DataTypeKind::kEnum));
}

TEST(DataTypeParsing, EnumDefaultWidth32) {
  DataType dt;
  dt.kind = DataTypeKind::kEnum;
  EXPECT_EQ(EvalTypeWidth(dt), 32u);
}

TEST(DataTypeParsing, EnumFirstNameDefaultsToZero) {
  auto r = Parse(
      "module m;\n"
      "  enum {A, B, C} x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& members = r.cu->modules[0]->items[0]->data_type.enum_members;
  ASSERT_EQ(members.size(), 3u);

  EXPECT_EQ(members[0].value, nullptr);

  EXPECT_EQ(members[1].value, nullptr);
  EXPECT_EQ(members[2].value, nullptr);
}

TEST(DataTypeParsing, EnumMixedValues) {
  auto r = Parse(
      "module m;\n"
      "  enum {a=3, b=7, c} x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& members = r.cu->modules[0]->items[0]->data_type.enum_members;
  ASSERT_EQ(members.size(), 3u);
  EXPECT_NE(members[0].value, nullptr);
  EXPECT_NE(members[1].value, nullptr);
  EXPECT_EQ(members[2].value, nullptr);
}

TEST(DataTypeParsing, Enum4StateBaseXZ) {
  auto r = Parse(
      "module m;\n"
      "  enum integer {IDLE=0, XX='x, S1=1, S2=2} state;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
