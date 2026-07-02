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

// §6.7.1 item b: a valid net data type may be a fixed-size unpacked structure
// whose members each have a valid (4-state) net data type. Declared here
// through a named unpacked-struct type, as in the item-a typedef example.
TEST(NetDataType, UnpackedStructNetIsValid) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct { logic [7:0] a; logic [7:0] b; } t;\n"
      "  wire t w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.7.1 item b: a fixed-size unpacked union whose members each have a valid
// (4-state) net data type is also a valid net data type, the union counterpart
// of the unpacked-struct case above.
TEST(NetDataType, UnpackedUnionNetIsValid) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef union { logic [7:0] a; logic [7:0] b; } t;\n"
      "  wire t w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetDataType, TwoStateBitIsRejected) {
  ElabFixture f;
  ElaborateSrc("module m; wire bit [3:0] b; endmodule\n", f);
  EXPECT_TRUE(f.has_errors);
}

// §6.7.1 item b (negative): an unpacked struct net is valid only when each
// member is itself a valid net type. A `real` member can never be a net, so the
// aggregate is rejected as a net data type.
TEST(NetDataType, UnpackedStructNetWithRealMemberIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire struct { logic [7:0] a; real r; } w;\n"
      "endmodule\n",
      f);
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

// §6.7.1 item a requires a *4-state* integral type (see §6.11.1). A packed
// structure is an integral type, but per §7.2.1 it is a 2-state vector when all
// of its members are 2-state, so it is not a legal net data type.
TEST(NetDataType, TwoStatePackedStructIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire struct packed { bit [3:0] lo; bit [3:0] hi; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// A packed structure with at least one 4-state member is a 4-state vector, so
// the same declaration shape is accepted once a `logic` member is present. This
// is the discriminating counterpart to the all-2-state rejection above: the
// 2-state `bit` member alone does not make the net illegal.
TEST(NetDataType, MixedStatePackedStructIsValid) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire struct packed { logic [3:0] lo; bit [3:0] hi; } s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
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

// §6.7.1: signing alone (no explicit data type) is the other implicit-logic
// input form -- `wire signed w` is a 1-bit signed logic net, distinct from the
// range-only form above.
TEST(NetDataType, ImplicitSignedNetIsLogic) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m; wire signed w; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* net = FindNet(design, "w");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(net->width, 1u);
  EXPECT_TRUE(net->is_signed);
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

// §6.7.1: an interconnect net shall specify at most one delay value. A single
// delay value is accepted.
TEST(InterconnectNet, SingleDelayIsAccepted) {
  ElabFixture f;
  ElaborateSrc("module m; interconnect #5 w; endmodule\n", f);
  EXPECT_FALSE(f.has_errors);
}

// §6.7.1 (negative): more than one delay value on an interconnect net is
// rejected.
TEST(InterconnectNet, MultipleDelayValuesRejected) {
  ElabFixture f;
  ElaborateSrc("module m; interconnect #(1, 2) w; endmodule\n", f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
