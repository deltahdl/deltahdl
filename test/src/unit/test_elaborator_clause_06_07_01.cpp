#include "common/types.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §6.7.1 net-declaration rules enforced by the elaborator. These tests drive
// the real Elaborator (via ElaborateSrc) so they observe the production code
// applying the rule, rather than a standalone model.

const RtlirNet* FindNet(const RtlirDesign* design, std::string_view name) {
  for (const auto& net : design->top_modules[0]->nets) {
    if (net.name == name) return &net;
  }
  return nullptr;
}

// --- Valid data type for a net (§6.7.1 list items a/b) ---
// A valid net data type shall be a 4-state integral type, or a fixed-size
// unpacked array/struct/union whose elements are themselves valid net types.

TEST(NetDataType, LogicIsValid) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m; wire logic [7:0] w; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetDataType, PackedStructIsValid) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire struct packed { logic ecc; logic [7:0] data; } memsig;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetDataType, TypedefToLogicIsValid) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef logic [31:0] addressT;\n"
      "  wire addressT w1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetDataType, FixedUnpackedArrayOfLogicIsValid) {
  ElabFixture f;
  ElaborateSrc("module m; wire logic w [0:3]; endmodule\n", f);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetDataType, TwoStateBitIsRejected) {
  ElabFixture f;
  ElaborateSrc("module m; wire bit [3:0] b; endmodule\n", f);
  EXPECT_TRUE(f.has_errors);
}

TEST(NetDataType, RealIsRejected) {
  ElabFixture f;
  ElaborateSrc("module m; wire real r; endmodule\n", f);
  EXPECT_TRUE(f.has_errors);
}

TEST(NetDataType, UnpackedArrayOfRealIsRejected) {
  ElabFixture f;
  ElaborateSrc("module m; wire real arr [0:3]; endmodule\n", f);
  EXPECT_TRUE(f.has_errors);
}

// --- Implicit logic data type (§6.7.1) ---
// When no data type is given (or only a range/signing), the net's data type is
// implicitly logic, so a plain `wire w` elaborates to a 1-bit 4-state net.

TEST(NetDataType, ImplicitNetIsSingleBit) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m; wire w; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* net = FindNet(design, "w");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(net->width, 1u);
}

TEST(NetDataType, ImplicitNetWithRangeMatchesExplicitLogic) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m; wire [15:0] ww; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* net = FindNet(design, "ww");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(net->width, 16u);
}

// --- Interconnect net restriction (§6.7.1) ---
// An interconnect net shall not have assignment expressions.

TEST(InterconnectNet, AssignmentExpressionIsRejected) {
  ElabFixture f;
  ElaborateSrc("module m; interconnect w = 1'b0; endmodule\n", f);
  EXPECT_TRUE(f.has_errors);
}

TEST(InterconnectNet, PlainInterconnectIsAccepted) {
  ElabFixture f;
  ElaborateSrc("module m; interconnect w; endmodule\n", f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
