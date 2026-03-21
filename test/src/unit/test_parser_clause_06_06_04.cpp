#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(TriregParsing, TriregDecl) {
  auto r = Parse(
      "module t;\n"
      "  trireg cap;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "cap");
}

TEST(TriregParsing, TriregDefaultInit) {
  auto r = Parse(
      "module t;\n"
      "  trireg t1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
}

TEST(TriregParsing, TriregChargeStrengthWithLogic) {
  auto r = Parse(
      "module t;\n"
      "  trireg (large) logic cap1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "cap1");
}

TEST(TriregParsing, TriregChargeStrengthSmall) {
  auto r = Parse(
      "module t;\n"
      "  trireg (small) s;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(item->data_type.charge_strength, 1u);
}

TEST(TriregParsing, TriregChargeStrengthMedium) {
  auto r = Parse(
      "module t;\n"
      "  trireg (medium) m;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(item->data_type.charge_strength, 2u);
}

TEST(TriregParsing, TriregChargeStrengthLarge) {
  auto r = Parse(
      "module t;\n"
      "  trireg (large) lg;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(item->data_type.charge_strength, 4u);
}

TEST(TriregParsing, TriregNoChargeStrength) {
  auto r = Parse(
      "module t;\n"
      "  trireg t1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.charge_strength, 0u);
}

TEST(TriregParsing, TriregVector) {
  auto r = Parse(
      "module t;\n"
      "  trireg [7:0] bus;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(item->name, "bus");
}

}  // namespace
