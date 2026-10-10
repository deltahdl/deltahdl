#include <gtest/gtest.h>

#include <initializer_list>
#include <string>
#include <string_view>

#include "common/source_loc.h"
#include "elaborator/net_data_type.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

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

// The rejecting counterpart of the typedef case above, and the pair is what
// tells a check that resolves the name from one that skips every name it sees.
// Skipping produces no error, which is what the accepting test expects, so that
// test alone reads the same either way. Here the name stands for `bit`, which
// §6.7.1 item a does not admit, and only a check that looked the name up can
// say so.
TEST(NetDataType, TypedefToTwoStateBitIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef bit [7:0] byteT;\n"
      "  wire byteT w;\n"
      "endmodule\n",
      f);
  // The report stands at the net declaration, not at the typedef the name
  // resolves through: ValidateNetDataTypeIs4State carries the net's own
  // location down the resolution.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be 4-state", 3, "6.7.1"));
}

// A name may stand for another name. The type reached at the end of the chain
// is the one §6.7.1 judges, so one lookup is not enough where a single test
// with one typedef would not notice the difference.
TEST(NetDataType, TypedefChainEndingInATwoStateTypeIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef bit [7:0] byteT;\n"
      "  typedef byteT wordT;\n"
      "  wire wordT w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be 4-state", 4, "6.7.1"));
}

// `real` is not an integral type at all, so it fails §6.7.1 item a for a
// different reason than a 2-state integral type does. Written out in full this
// is already rejected; written as a name it reaches the same rule by the path a
// name takes.
TEST(NetDataType, TypedefToRealIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef real realT;\n"
      "  wire realT w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be 4-state", 3, "6.7.1"));
}

// An enumeration named by a typedef, with a 2-state base. The enum rule is
// tested above on an enumeration written out in the net declaration; this asks
// the same question of one that arrives as a name.
TEST(NetDataType, TypedefToEnumWithTwoStateBaseIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef enum bit [1:0] { RED, GREEN, BLUE } colorT;\n"
      "  wire colorT w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be 4-state", 3, "6.7.1"));
}

// The same enumeration with a 4-state base, named the same way. Without this a
// check that rejected every enumeration reached through a name would pass the
// rejection above, and the rule is about the base rather than about the name.
TEST(NetDataType, TypedefToEnumWithFourStateBaseIsValid) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef enum logic [1:0] { RED, GREEN, BLUE } colorT;\n"
      "  wire colorT w;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// A packed structure whose members are all 2-state, named by a typedef. §7.2.1
// makes it a 2-state vector, which §6.7.1 item a does not admit, and the
// mixed-state twin below is accepted through the same name.
TEST(NetDataType, TypedefToAllTwoStatePackedStructIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { bit [3:0] lo; bit [3:0] hi; } wordT;\n"
      "  wire wordT w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be 4-state", 3, "6.7.1"));
}

TEST(NetDataType, TypedefToMixedStatePackedStructIsValid) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [3:0] lo; bit [3:0] hi; } wordT;\n"
      "  wire wordT w;\n"
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be 4-state", 1, "6.7.1"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unpacked struct/union net member must be a valid net data type", 2,
      "6.7.1"));
}

TEST(NetDataType, RealIsRejected) {
  ElabFixture f;
  ElaborateSrc("module m; wire real r; endmodule\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be 4-state", 1, "6.7.1"));
}

TEST(NetDataType, UnpackedArrayOfRealIsRejected) {
  ElabFixture f;
  ElaborateSrc("module m; wire real arr [0:3]; endmodule\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be 4-state", 1, "6.7.1"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be 4-state", 2, "6.7.1"));
}

// §6.19: an enumeration declared with no data type takes int, and the clause's
// own example calls `enum {red, yellow, green}` an "anonymous int type". int is
// 2-state, so an enumeration written with no base is not a valid net data type
// under §6.7.1 item a.
TEST(NetDataType, EnumWithNoBaseIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire enum { RED, GREEN, BLUE } e;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be 4-state", 2, "6.7.1"));
}

// The discriminating counterpart: the same enumeration, given a 4-state base,
// is a valid net data type. Without this test a check that rejected every enum
// net would pass the rejection above, and the rule being implemented is about
// the base rather than about the enum.
TEST(NetDataType, EnumWithFourStateBaseIsValid) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire enum logic [1:0] { RED, GREEN, BLUE } e;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// The third leg: a base that is present and 2-state. The no-base case above
// reaches the rule through an unset base kind and this one through a base kind
// that is set, so neither stands in for the other.
TEST(NetDataType, EnumWithTwoStateBaseIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire enum bit [1:0] { RED, GREEN, BLUE } e;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be 4-state", 2, "6.7.1"));
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
// An interconnect net takes no value in its own declaration.

TEST(InterconnectNet, AssignmentExpressionIsRejected) {
  ElabFixture f;
  ElaborateSrc("module m; interconnect w = 1'b0; endmodule\n", f);
  // LowerNetDeclAssignment files this under §10.3.1, which is where the net
  // declaration assignment the interconnect net may not have is stated.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "an interconnect net cannot be given a value where it is declared", 1,
      "10.3.1"));
}

TEST(InterconnectNet, PlainInterconnectIsAccepted) {
  ElabFixture f;
  ElaborateSrc("module m; interconnect w; endmodule\n", f);
  EXPECT_FALSE(f.has_errors);
}

// §6.7.1: one delay value is the limit for an interconnect net. A single
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an interconnect net accepts one delay value, and "
                            "this declaration gives more",
                            1, "6.7.1"));
}

// §6.7.1 (printed page 103 of IEEE 1800-2023) admits a packed structure
// as a net's data type, and §7.2.1 (printed 147) lays its members out as
// windows of the vector, which the simulator needs the members' order and
// widths for. The net record carries the resolved aggregate for a typedef name
// standing for a structure: the two members in declaration order beside the
// 32-bit width. A net record carrying the width alone leaves every member
// select of the net unresolvable.
TEST(NetDataType, TypedefStructNetCarriesItsAggregate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [7:0] opcode; logic [23:0] imm; } "
      "instruction_t;\n"
      "  wire instruction_t w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* net = FindNet(design, "w");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(net->width, 32u);
  ASSERT_NE(net->dtype, nullptr);
  ASSERT_EQ(net->dtype->struct_members.size(), 2u);
  EXPECT_EQ(net->dtype->struct_members[0].name, "opcode");
  EXPECT_EQ(net->dtype->struct_members[1].name, "imm");
}

// The typedef reached through an explicit import (§26.3), which enters the
// package's typedef under its bare name, and through the anonymous form of
// §6.7.1's own example, which writes the structure in the declaration: both
// carry the aggregate. A resolution that took the declaration's own kind alone
// would carry the anonymous structure and miss the imported name.
TEST(NetDataType, ImportedAndAnonymousStructNetsCarryTheirAggregates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package A;\n"
      "  typedef struct packed { logic [7:0] opcode; logic [23:0] imm; } "
      "instruction_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import A::instruction_t;\n"
      "  wire instruction_t w;\n"
      "  wire struct packed { logic ecc; logic [7:0] data; } memsig;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* w = FindNet(design, "w");
  ASSERT_NE(w, nullptr);
  ASSERT_NE(w->dtype, nullptr);
  EXPECT_EQ(w->dtype->struct_members.size(), 2u);
  auto* memsig = FindNet(design, "memsig");
  ASSERT_NE(memsig, nullptr);
  EXPECT_EQ(memsig->width, 9u);
  ASSERT_NE(memsig->dtype, nullptr);
  ASSERT_EQ(memsig->dtype->struct_members.size(), 2u);
  EXPECT_EQ(memsig->dtype->struct_members[0].name, "ecc");
}

// A net that is an array of the structure rather than one of it keeps the
// width alone, as a port of the same shape does: an unpacked dimension makes
// the net an array of elements (§7.4.2), and a use-site packed dimension
// stacks on the type (§7.4.4), so the record carries the declaration's own
// type for its range and no member layout. Carrying the aggregate for either
// would lay one element's members over the whole array.
TEST(NetDataType, StructNetWithADimensionCarriesNoAggregate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [7:0] opcode; logic [23:0] imm; } "
      "instruction_t;\n"
      "  wire instruction_t u [2];\n"
      "  wire instruction_t [1:0] v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u = FindNet(design, "u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->dtype, nullptr);
  auto* v = FindNet(design, "v");
  ASSERT_NE(v, nullptr);
  ASSERT_NE(v->dtype, nullptr);
  EXPECT_NE(v->dtype->packed_dim_left, nullptr);
  EXPECT_TRUE(v->dtype->struct_members.empty());
}

// --- Fixed-size unpacked dimensions (Syntax 6-2 and §6.7.1 item b) ---
// A net declarator takes unpacked_dimension, a constant range or size, and
// never the variable_dimension a variable declarator takes. Each case below
// writes one of the four variable forms, so a check that recognised only some
// of them is caught by the form it missed.

void ExpectNetDimensionReported(const std::string& items) {
  ElabFixture f;
  const std::string kSrc = "module m;\n" + items + "\nendmodule\n";
  ElaborateSrc(kSrc, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a net's unpacked dimension must be fixed-size",
                            LineHolding(kSrc, "wire logic w"), "6.7"));
}

TEST(NetDataType, DynamicDimensionOnANetIsRejected) {
  ExpectNetDimensionReported("  wire logic w[];");
}

TEST(NetDataType, QueueDimensionOnANetIsRejected) {
  ExpectNetDimensionReported("  wire logic w[$];");
}

TEST(NetDataType, AssociativeDimensionOnANetIsRejected) {
  ExpectNetDimensionReported("  wire logic w[int];");
}

TEST(NetDataType, WildcardAssociativeDimensionOnANetIsRejected) {
  ExpectNetDimensionReported("  wire logic w[*];");
}

// An associative index may be a user-defined type, a typedef or a class, which
// the parser keeps as the bare name a parameter-sized dimension is kept as.
TEST(NetDataType, TypedefIndexedDimensionOnANetIsRejected) {
  ExpectNetDimensionReported("  typedef int k_t;\n  wire logic w[k_t];");
}

TEST(NetDataType, ClassIndexedDimensionOnANetIsRejected) {
  ExpectNetDimensionReported("  class K; endclass\n  wire logic w[K];");
}

// A net of a user-defined nettype is declared by the same net_decl_assignment,
// so its declarator is held to the same dimension.
TEST(NetDataType, QueueDimensionOnANettypeNetIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  nettype logic [3:0] nt;\n"
      "  nt w[$];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a net's unpacked dimension must be fixed-size", 3,
                            "6.7"));
}

// A typedef carries its unpacked dimensions into the type it names, so a net
// declared through one is an array of that shape, and item b requires it to be
// fixed-size.
TEST(NetDataType, TypedefOfADynamicArrayIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef logic da_t[];\n"
      "  wire da_t w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be a fixed-size array", 3,
                            "6.7.1"));
}

// The counterparts: a dimension sized by a parameter is a constant size, and a
// typedef of a fixed-size array names a fixed-size array, so neither is
// confused with the variable forms above.
TEST(NetDataType, ParameterSizedDimensionAndFixedArrayTypedefAreValid) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter int N = 3;\n"
      "  typedef logic fa_t[2];\n"
      "  wire logic w[N];\n"
      "  wire fa_t v;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// --- Members of a structure or union net (§6.7.1 items a and b) ---

// Item b is recursive: an unpacked structure is a valid net data type only when
// each member is, and a 2-state member is not, whether written as a keyword or
// named through a typedef.
TEST(NetDataType, UnpackedStructNetWithATwoStateMemberIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire struct { logic [3:0] a; bit b; } w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unpacked struct/union net member must be a valid net data type", 2,
      "6.7.1"));
}

TEST(NetDataType, UnpackedStructNetWithATypedefTwoStateMemberIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int i_t;\n"
      "  wire struct { logic [3:0] a; i_t b; } w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unpacked struct/union net member must be a valid net data type", 3,
      "6.7.1"));
}

// A member that is itself a packed structure is judged as one: all-2-state
// members make it 2-state, and the union holding it is no net data type.
TEST(NetDataType, UnpackedUnionNetWithATwoStatePackedStructMemberIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire union { logic [7:0] a; struct packed { bit [7:0] x; } b; } w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unpacked struct/union net member must be a valid net data type", 2,
      "6.7.1"));
}

// The counterpart: members named through a 4-state typedef, and a nested
// unpacked structure of 4-state members, are valid net data types.
TEST(NetDataType, UnpackedStructNetWithFourStateNamedAndNestedMembersIsValid) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef logic [3:0] n_t;\n"
      "  wire struct { n_t a; struct { logic c; } s; } w;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// Item a: a packed structure is 4-state only when a member is, and a member
// named through a typedef or nested as a packed structure is 4-state only when
// what it stands for is. Here every member resolves to a 2-state type.
TEST(NetDataType, PackedStructNetWithTwoStateTypedefMembersIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef bit [3:0] nib_t;\n"
      "  wire struct packed { nib_t a; bit b; } w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be 4-state", 3, "6.7.1"));
}

TEST(NetDataType, PackedStructNetWithATwoStateNestedStructIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire struct packed { struct packed { bit x; } s; int b; } w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be 4-state", 2, "6.7.1"));
}

// An enumeration member is as 4-state as its base, so a 2-state base leaves the
// packed structure 2-state.
TEST(NetDataType, PackedStructNetWithATwoStateEnumMemberIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef enum bit [1:0] { A, B } e_t;\n"
      "  wire struct packed { e_t e; bit b; } w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be 4-state", 3, "6.7.1"));
}

// The counterpart: one 4-state member, named or nested, makes the packed
// structure 4-state, whatever the other members are.
TEST(NetDataType, PackedStructNetWithFourStateNamedOrNestedMembersIsValid) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef logic [3:0] nib_t;\n"
      "  wire struct packed { nib_t a; bit b; } w;\n"
      "  wire struct packed { struct packed { logic x; } s; int b; } v;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// A soft union is packed (§7.3.1), so it is judged by item a as a packed
// structure is: all-2-state members make it a 2-state type.
TEST(NetDataType, TwoStateSoftUnionNetIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire union soft { bit [3:0] a; bit [1:0] b; } w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be 4-state", 2, "6.7.1"));
}

// A typedef table can hold what no source the elaborator accepts gives it:
// names that lead to each other in a cycle, and member types, direct or through
// a typedef, that name nothing in the table. Such a type leaves nothing to
// judge, so none of these is reported and none loops.
TEST(NetDataType, TypesResolvingToNothingAreNotReported) {
  ElabFixture f;
  DataType to_b;
  to_b.kind = DataTypeKind::kNamed;
  to_b.type_name = "b_t";
  DataType to_a = to_b;
  to_a.type_name = "a_t";
  DataType to_missing = to_b;
  to_missing.type_name = "missing_t";
  StructMember missing;
  missing.type_kind = DataTypeKind::kNamed;
  missing.type_name = "missing_t";
  StructMember dangling = missing;
  dangling.type_name = "dangling_t";
  DataType packed_missing;
  packed_missing.kind = DataTypeKind::kStruct;
  packed_missing.is_packed = true;
  packed_missing.struct_members = {missing};
  DataType packed_dangling = packed_missing;
  packed_dangling.struct_members = {dangling};
  DataType unpacked;
  unpacked.kind = DataTypeKind::kStruct;
  unpacked.struct_members = {missing, dangling};
  const TypedefMap kTable{
      {"a_t", to_b}, {"b_t", to_a}, {"dangling_t", to_missing}};

  for (const DataType* type :
       {&to_a, &packed_missing, &packed_dangling, &unpacked}) {
    ValidateNetDataTypeIs4State(*type, kTable, f.diag, SourceLoc{});
  }
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

}  // namespace
