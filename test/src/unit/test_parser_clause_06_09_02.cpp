

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_net_declaration.h"

using namespace delta;

namespace {

TEST(ParserA213, NetDeclVectored) {
  auto r = Parse("module m; wire vectored [7:0] bus; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA213, NetDeclScalared) {
  auto r = Parse("module m; wire scalared [7:0] bus; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection6, Sec6_7_1_ScalaredWithExplicitType) {
  auto r = Parse(
      "module t;\n"
      "  wire scalared logic [7:0] s;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_TRUE(item->data_type.is_scalared);
  EXPECT_EQ(item->name, "s");
}

TEST(ParserSection6, Sec6_7_1_WireVectoredQualifier) {
  auto r = Parse(
      "module t;\n"
      "  wire vectored [7:0] v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_vectored);
  EXPECT_EQ(item->name, "v");
}

TEST(ParserSection6, Sec6_7_1_WireScalaredQualifier) {
  auto r = Parse(
      "module t;\n"
      "  wire scalared [7:0] sc;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_scalared);
  EXPECT_EQ(item->name, "sc");
}

TEST(ParserSection6, Sec6_9_2_Tri1ScalaredBus) {
  auto r = Parse(
      "module t;\n"
      "  tri1 scalared [63:0] bus64;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTri1);
  EXPECT_TRUE(item->data_type.is_scalared);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 63u);
}

TEST(ParserSection6, Sec6_9_2_TriVectoredData) {
  auto r = Parse(
      "module t;\n"
      "  tri vectored [31:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTri);
  EXPECT_TRUE(item->data_type.is_vectored);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 31u);
}

TEST(ParserSection6, Sec6_9_2_VectoredWithoutPackedDim) {
  NetDeclInfo info;
  info.is_vectored = true;
  info.packed_dim_count = 0;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(ParserSection6, Sec6_9_2_ScalaredWithoutPackedDim) {
  NetDeclInfo info;
  info.is_scalared = true;
  info.packed_dim_count = 0;
  EXPECT_FALSE(ValidateNetDecl(info));
}

}
