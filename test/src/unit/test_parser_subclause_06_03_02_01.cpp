

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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

TEST(DataTypeParsing, TriregChargeStrengthMedium) {
  auto r = Parse(
      "module t;\n"
      "  trireg (medium) m;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(item->data_type.charge_strength, 2);
  EXPECT_EQ(item->name, "m");
}

// Only small/medium/large name a charge strength. A drive-strength keyword
// such as weak is not in the charge-strength set, so the parser declines to
// consume the parenthesized group and the declaration fails.
TEST(DataTypeParsing, DriveStrengthKeywordIsNotChargeStrength) {
  auto r = Parse(
      "module t;\n"
      "  trireg (weak) c;\n"
      "endmodule\n");
  // §6.7 owns the net declaration list, and that is where the declaration
  // fails: ParseChargeStrength puts the position back on the '(' it could not
  // read as small, medium or large, so no §6.3.2.1 report is written here.
  EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got '('", 2, "6.7"));
}

TEST(DataTypeParsing, ChargeStrengthKeywordOnWireFails) {
  auto r = Parse(
      "module t;\n"
      "  wire (small) w;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "charge strength can only be used with trireg nets",
                            2, "6.3.2.1"));
}

}  // namespace
