#include "common/types.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

const RtlirNet* FindNet(const RtlirDesign* design, std::string_view name) {
  for (const auto& net : design->top_modules[0]->nets) {
    if (net.name == name) return &net;
  }
  return nullptr;
}

TEST(NetDecl, TriregWithoutChargeStrengthOk) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m; trireg t; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* net = FindNet(design, "t");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(net->net_type, NetType::kTrireg);
}

TEST(NetDecl, TriregChargeSmallProducesSmallStrength) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m; trireg (small) t; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* net = FindNet(design, "t");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(net->charge_strength, Strength::kSmall);
}

TEST(NetDecl, TriregChargeMediumProducesMediumStrength) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m; trireg (medium) t; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* net = FindNet(design, "t");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(net->charge_strength, Strength::kMedium);
}

TEST(NetDecl, TriregChargeLargeProducesLargeStrength) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m; trireg (large) t; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* net = FindNet(design, "t");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(net->charge_strength, Strength::kLarge);
}

TEST(NetDecl, VectoredWithPackedDimOk) {
  ElabFixture f;
  auto* design =
      ElaborateSrc("module m; wire vectored [3:0] w; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* net = FindNet(design, "w");
  ASSERT_NE(net, nullptr);
  EXPECT_TRUE(net->is_vectored);
}

TEST(NetDecl, ScalaredWithPackedDimOk) {
  ElabFixture f;
  auto* design =
      ElaborateSrc("module m; wire scalared [3:0] w; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* net = FindNet(design, "w");
  ASSERT_NE(net, nullptr);
  EXPECT_TRUE(net->is_scalared);
}

TEST(NetDecl, VectoredWithoutPackedDimEmitsError) {
  ElabFixture f;
  ElaborateSrc("module m; wire vectored w; endmodule\n", f);
  EXPECT_TRUE(f.has_errors);
}

TEST(NetDecl, ScalaredWithoutPackedDimEmitsError) {
  ElabFixture f;
  ElaborateSrc("module m; wire scalared w; endmodule\n", f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
