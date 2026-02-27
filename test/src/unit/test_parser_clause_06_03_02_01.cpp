// §6.3.2.1: Charge strength

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA213, NetDeclTriregChargeStrength) {
  auto r = Parse("module m; trireg (medium) net1; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA222, ChargeStrengthMedium) {
  // trireg (medium)
  auto r = Parse(
      "module m;\n"
      "  trireg (medium) t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.charge_strength, 2u);
}

// --- Charge strength only on trireg ---
TEST(ParserA222, ChargeStrengthNoSpecDefault) {
  // trireg without charge_strength
  auto r = Parse(
      "module m;\n"
      "  trireg t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.charge_strength, 0u);
}

}  // namespace
