#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

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
  EXPECT_EQ(item->typedef_type.struct_members[2].type_kind,
            DataTypeKind::kByte);
}

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

TEST(UnionParsing, PackedDimensionOnUnion) {
  auto r = Parse(
      "module t;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } [3:0] arr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->data_type.is_packed);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_NE(item->data_type.packed_dim_right, nullptr);
}

TEST(UnionParsing, UnionOfStructsSharingInitialSequence) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int kind; int a; } pa_t;\n"
      "  typedef struct { int kind; int b; int c; } pb_t;\n"
      "  typedef union { pa_t pa; pb_t pb; } u_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UnionParsing, UnionSoftAlternative) {
  auto r = Parse(
      "module t;\n"
      "  typedef union soft {\n"
      "    int a;\n"
      "    logic [7:0] b;\n"
      "  } u_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->typedef_type.is_soft);
  EXPECT_FALSE(item->typedef_type.is_tagged);
}

TEST(UnionParsing, UnionTaggedAlternative) {
  auto r = Parse(
      "module t;\n"
      "  typedef union tagged {\n"
      "    int a;\n"
      "    shortreal b;\n"
      "  } u_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->typedef_type.is_tagged);
  EXPECT_FALSE(item->typedef_type.is_soft);
}

TEST(UnionParsing, VoidMemberParses) {
  auto r = Parse(
      "module t;\n"
      "  typedef union tagged {\n"
      "    void none;\n"
      "    int val;\n"
      "  } u_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2u);
  EXPECT_EQ(item->typedef_type.struct_members[0].type_kind,
            DataTypeKind::kVoid);
}

TEST(UnionParsing, RandomQualifierOnMemberParses) {
  auto r = Parse(
      "module t;\n"
      "  typedef union {\n"
      "    rand int a;\n"
      "    int b;\n"
      "  } u_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2u);
  EXPECT_TRUE(item->typedef_type.struct_members[0].is_rand);
  EXPECT_FALSE(item->typedef_type.struct_members[1].is_rand);
}

TEST(UnionParsing, RandcQualifierOnMemberParses) {
  auto r = Parse(
      "module t;\n"
      "  typedef union {\n"
      "    randc int a;\n"
      "    int b;\n"
      "  } u_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2u);
  EXPECT_TRUE(item->typedef_type.struct_members[0].is_randc);
}

TEST(UnionParsing, MultipleDeclaratorsInOneMemberLine) {
  auto r = Parse(
      "module t;\n"
      "  typedef union {\n"
      "    int a, b;\n"
      "  } u_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2u);
  EXPECT_EQ(item->typedef_type.struct_members[0].name, "a");
  EXPECT_EQ(item->typedef_type.struct_members[1].name, "b");
}

TEST(UnionParsing, AttributeInstanceOnMember) {
  auto r = Parse(
      "module t;\n"
      "  typedef union {\n"
      "    (* keep *) int a;\n"
      "    int b;\n"
      "  } u_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2u);
  EXPECT_FALSE(item->typedef_type.struct_members[0].attrs.empty());
}

}  // namespace
