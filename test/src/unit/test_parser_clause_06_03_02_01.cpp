

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DataTypeParsing, TriregChargeStrengthLarge) {
  auto r = Parse(
      "module t;\n"
      "  trireg (large) l1;\n"
      "endmodule\n");
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.charge_strength, 4);
}

TEST(DataTypeParsing, TriregChargeStrengthWithDelay) {
  auto r = Parse(
      "module t;\n"
      "  trireg (large) #(0, 0, 50) cap1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(item->data_type.charge_strength, 4);
  EXPECT_EQ(item->name, "cap1");
  EXPECT_NE(item->net_delay_decay, nullptr);
}

TEST(DataTypeParsing, TriregNoChargeStrengthParserDefault) {
  auto r = Parse(
      "module t;\n"
      "  trireg a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(item->data_type.charge_strength, 0);
}

TEST(DataTypeParsing, TriregChargeStrengthMedium) {
  auto r = Parse(
      "module t;\n"
      "  trireg (medium) m1;\n"
      "endmodule\n");
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(item->data_type.charge_strength, 2);
}

TEST(DataTypeParsing, TriregChargeStrengthSmall) {
  auto r = Parse(
      "module t;\n"
      "  trireg (small) s1;\n"
      "endmodule\n");
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(item->data_type.charge_strength, 1);
}

TEST(DataTypeParsing, TriregChargeStrengthLargeWithLogicAndDelay) {
  auto r = Parse(
      "module t;\n"
      "  trireg (large) logic #(0,0,0) cap1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_NE(item->data_type.charge_strength, 0u);
  EXPECT_EQ(item->name, "cap1");
}

TEST(DataTypeParsing, TriregChargeStrengthSignedVector) {
  auto r = Parse(
      "module t;\n"
      "  trireg (small) signed [3:0] cap2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(item->data_type.charge_strength, 1);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "cap2");
}

}  // namespace
