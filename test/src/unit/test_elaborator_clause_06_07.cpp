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

TEST(NetDecl, VectoredWithSingleBitPackedDimOk) {
  // A single-bit packed range still satisfies "at least one packed dimension":
  // the accept path here rides the packed-dimension guard, not a width > 1
  // shortcut, since [0:0] is one bit wide.
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
  // scalared counterpart of the width-1 packed-dimension accept: the guard
  // recognizes a present packed range independent of its width.
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
  // §6.11.1 dependency: the packed dimension may come from a 4-state packed
  // structure rather than an inline range. The struct's bits give the net a
  // width greater than one, so the vectored net is accepted even though no
  // range dimension sits on the declaration itself.
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
  EXPECT_TRUE(f.has_errors);
}

TEST(NetDecl, ScalaredWithoutPackedDimEmitsError) {
  ElabFixture f;
  ElaborateSrc("module m; wire scalared w; endmodule\n", f);
  EXPECT_TRUE(f.has_errors);
}

TEST(NetDecl, VectoredWithOnlyUnpackedDimEmitsError) {
  // An unpacked dimension is not a packed one: a post-name range does not
  // satisfy the requirement, so vectored with only an unpacked dimension is
  // still rejected.
  ElabFixture f;
  ElaborateSrc("module m; wire vectored w [3:0]; endmodule\n", f);
  EXPECT_TRUE(f.has_errors);
}

TEST(NetDecl, ScalaredWithOnlyUnpackedDimEmitsError) {
  ElabFixture f;
  ElaborateSrc("module m; wire scalared w [3:0]; endmodule\n", f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
