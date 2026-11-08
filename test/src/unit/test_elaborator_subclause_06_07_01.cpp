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

const RtlirNet* FindNet(const RtlirDesign* design, std::string_view name) {
  for (const auto& net : design->top_modules[0]->nets) {
    if (net.name == name) return &net;
  }
  return nullptr;
}

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

TEST(NetDataType, TypedefToTwoStateBitIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef bit [7:0] byteT;\n"
      "  wire byteT w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be 4-state", 3, "6.7.1"));
}

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

TEST(NetDataType, EnumWithFourStateBaseIsValid) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire enum logic [1:0] { RED, GREEN, BLUE } e;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

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

TEST(NetDataType, MixedStatePackedStructIsValid) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire struct packed { logic [3:0] lo; bit [3:0] hi; } s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

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

TEST(InterconnectNet, AssignmentExpressionIsRejected) {
  ElabFixture f;
  ElaborateSrc("module m; interconnect w = 1'b0; endmodule\n", f);
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

TEST(InterconnectNet, SingleDelayIsAccepted) {
  ElabFixture f;
  ElaborateSrc("module m; interconnect #5 w; endmodule\n", f);
  EXPECT_FALSE(f.has_errors);
}

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

TEST(NetDataType, TypedefIndexedDimensionOnANetIsRejected) {
  ExpectNetDimensionReported("  typedef int k_t;\n  wire logic w[k_t];");
}

TEST(NetDataType, ClassIndexedDimensionOnANetIsRejected) {
  ExpectNetDimensionReported("  class K; endclass\n  wire logic w[K];");
}

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
