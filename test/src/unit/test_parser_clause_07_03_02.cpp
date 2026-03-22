#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TaggedUnionParsing, TaggedUnionVariable) {
  auto r = Parse(
      "module m;\n"
      "  union tagged { int a; real b; } u;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->data_type.is_tagged);
}
TEST(TaggedUnionParsing, TaggedUnionTypedef) {
  auto r = Parse(
      "module t;\n"
      "  typedef union tagged {\n"
      "    void Invalid;\n"
      "    int Valid;\n"
      "  } VInt;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->typedef_type.is_tagged);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 2u);
}

TEST(TaggedUnionParsing, UnionWithNestedStruct) {
  auto r = Parse(
      "module t;\n"
      "  typedef union tagged {\n"
      "    struct {\n"
      "      bit [4:0] reg1, reg2;\n"
      "    } Add;\n"
      "    bit [9:0] Jmp;\n"
      "  } Instr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->typedef_type.is_tagged);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 2u);
}

TEST(TaggedUnionParsing, TaggedUnionVoidMember) {
  auto r = Parse(
      "module t;\n"
      "  typedef union tagged {\n"
      "    void Invalid;\n"
      "    int Valid;\n"
      "  } VInt;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_tagged);
  EXPECT_EQ(item->typedef_type.struct_members[0].type_kind,
            DataTypeKind::kVoid);
  EXPECT_EQ(item->typedef_type.struct_members[0].name, "Invalid");
}

// §7.3.2: tagged + packed qualifiers together.
TEST(TaggedUnionParsing, PackedTaggedUnion) {
  auto r = Parse(
      "module t;\n"
      "  typedef union tagged packed {\n"
      "    bit [7:0] A;\n"
      "    bit [15:0] B;\n"
      "  } PU;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->typedef_type.is_tagged);
  EXPECT_TRUE(item->typedef_type.is_packed);
}

// §7.3.2: tagged union with three members.
TEST(TaggedUnionParsing, TaggedUnionThreeMembers) {
  auto r = Parse(
      "module t;\n"
      "  typedef union tagged {\n"
      "    void None;\n"
      "    int Value;\n"
      "    real Float;\n"
      "  } Opt;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_tagged);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 3u);
}

}  // namespace
