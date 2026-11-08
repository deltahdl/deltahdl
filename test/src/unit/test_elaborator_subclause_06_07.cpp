#include <gtest/gtest.h>

#include <string_view>

#include "common/types.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

TEST(NetDecl, VectoredWithSingleBitPackedDimOk) {
  ElabFixture f;
  auto* design =
      ElaborateSrc("module m; wire vectored [0:0] w; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* net = FindNet(design, "w");
  ASSERT_NE(net, nullptr);
  EXPECT_TRUE(net->is_vectored);
}

TEST(NetDecl, ScalaredWithSingleBitPackedDimOk) {
  ElabFixture f;
  auto* design =
      ElaborateSrc("module m; wire scalared [0:0] w; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* net = FindNet(design, "w");
  ASSERT_NE(net, nullptr);
  EXPECT_TRUE(net->is_scalared);
}

TEST(NetDecl, VectoredPackedStructNetSatisfiesPackedRequirement) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire vectored struct packed { logic [3:0] a; logic [3:0] b; } w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* net = FindNet(design, "w");
  ASSERT_NE(net, nullptr);
  EXPECT_TRUE(net->is_vectored);
}

TEST(NetDecl, VectoredWithoutPackedDimEmitsError) {
  ElabFixture f;
  ElaborateSrc("module m; wire vectored w; endmodule\n", f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "vectored or scalared requires at least one packed dimension", 1,
      "6.9.2"));
}

TEST(NetDecl, ScalaredWithoutPackedDimEmitsError) {
  ElabFixture f;
  ElaborateSrc("module m; wire scalared w; endmodule\n", f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "vectored or scalared requires at least one packed dimension", 1,
      "6.9.2"));
}

TEST(NetDecl, VectoredWithOnlyUnpackedDimEmitsError) {
  ElabFixture f;
  ElaborateSrc("module m; wire vectored w [3:0]; endmodule\n", f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "vectored or scalared requires at least one packed dimension", 1,
      "6.9.2"));
}

TEST(NetDecl, ScalaredWithOnlyUnpackedDimEmitsError) {
  ElabFixture f;
  ElaborateSrc("module m; wire scalared w [3:0]; endmodule\n", f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "vectored or scalared requires at least one packed dimension", 1,
      "6.9.2"));
}

TEST(NetDeclElaboration, ParameterBoundInPackedRangeSizesTheNet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int N = 4;\n"
      "  wire [N-1:0] bus;\n"
      "  logic [N-1:0] var_bus;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* net = FindNet(design, "bus");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(net->width, 4u);
}

}  // namespace
