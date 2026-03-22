#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(UnionParsing, UnionBasic) {
  auto r = Parse(
      "module t;\n"
      "  typedef union {\n"
      "    int i;\n"
      "    shortreal f;\n"
      "  } num;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 2u);
}

// §7.3: Union is unpacked by default (no packed keyword).
TEST(UnionParsing, UnionDefaultNotPacked) {
  auto r = Parse(
      "module t;\n"
      "  typedef union {\n"
      "    int i;\n"
      "    shortreal f;\n"
      "  } num;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  EXPECT_FALSE(item->typedef_type.is_packed);
  EXPECT_FALSE(item->typedef_type.is_tagged);
  EXPECT_FALSE(item->typedef_type.is_soft);
}

// §7.3: Union member type kinds are preserved in AST.
TEST(UnionParsing, UnionMemberTypeKinds) {
  auto r = Parse(
      "module t;\n"
      "  typedef union {\n"
      "    int i;\n"
      "    logic [31:0] l;\n"
      "    byte b;\n"
      "  } multi_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 3u);
  EXPECT_EQ(item->typedef_type.struct_members[0].type_kind, DataTypeKind::kInt);
  EXPECT_EQ(item->typedef_type.struct_members[1].type_kind,
            DataTypeKind::kLogic);
  EXPECT_EQ(item->typedef_type.struct_members[2].type_kind, DataTypeKind::kByte);
}

// §7.3 LRM example: anonymous union nested inside a struct.
TEST(UnionParsing, AnonymousUnionInStruct) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct {\n"
      "    bit isfloat;\n"
      "    union { int i; shortreal f; } n;\n"
      "  } tagged_st;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2u);
  EXPECT_EQ(item->typedef_type.struct_members[1].type_kind,
            DataTypeKind::kUnion);
}

}  // namespace
