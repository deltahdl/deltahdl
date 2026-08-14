#include "common/types.h"
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

// §6.7's net_declaration production admits vectored and scalared but states no
// obligation about either. §6.9.2 is the sentence that confines the two
// keywords to "vector net declarations", so ValidateVectoredScalaredNet in
// src/elaborator/elaborator_decls.cpp files the report under §6.9.2 and the
// four cases below name that subclause rather than the one this file covers.
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
  // An unpacked dimension is not a packed one: a post-name range does not
  // satisfy the requirement, so vectored with only an unpacked dimension is
  // still rejected.
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

// §6.7 lets a net declaration carry a packed dimension, and §6.20.2 makes a
// parameter a constant, so a parameter is legal as one of that dimension's
// bounds. The range has a size only once the parameter is folded, and a
// declaration that names one must end up as wide as the value it resolves to --
// four bits here, not the single bit an unfolded range would leave. The
// variable declared alongside it pins the claim to nets: both ranges are
// written the same way and read the same parameter, so a width that differs
// between them is about the net path and nothing else.
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
