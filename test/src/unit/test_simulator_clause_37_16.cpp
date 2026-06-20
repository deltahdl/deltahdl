#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.16 Nets: the VPI net object model, the net counterpart of §37.17's
// variable model. These tests observe the production helpers in vpi.cpp that
// apply the numbered "Details" of the clause. The range relations (details 1
// and 26) are woven onto §37.22's range helpers, so an empty dimension behaves
// the same here as it does there.
//
// The driver/load/port iteration details (4, 6-8, 14-20, 22) describe the
// behavior of a connectivity and force/assign engine that the VPI layer does
// not model with a live driver graph, so they carry no production rule of their
// own here; the ownable classification rules they rest on (e.g. detail 5,
// detail 11's driver-iteration gate) are exercised below.

// D1: a net declared as an array with one or more unpacked ranges is an array
// net; a packed struct/union or enum net with one or more explicit packed
// ranges is a packed array net.
TEST(NetModel, ArrayNetAndPackedArrayNetClassification) {
  EXPECT_TRUE(VpiIsArrayNet(1));
  EXPECT_TRUE(VpiIsArrayNet(2));
  EXPECT_FALSE(VpiIsArrayNet(0));

  EXPECT_TRUE(VpiIsPackedArrayNet(vpiStructNet, 1));
  EXPECT_TRUE(VpiIsPackedArrayNet(vpiUnionNet, 2));
  EXPECT_TRUE(VpiIsPackedArrayNet(vpiEnumNet, 1));
  // No explicit packed range -> not a packed array net.
  EXPECT_FALSE(VpiIsPackedArrayNet(vpiStructNet, 0));
  // A logic net is not one of the packed-array-net base kinds.
  EXPECT_FALSE(VpiIsPackedArrayNet(vpiNet, 1));
}

// D2: vpiArrayMember is TRUE when the net's vpiParent prefix is an array net.
TEST(NetModel, ArrayMemberReadsArrayNetParent) {
  VpiObject array_net;
  array_net.type = vpiNetArray;
  VpiObject element;
  element.type = vpiNet;
  element.parent = &array_net;
  EXPECT_TRUE(VpiNetIsArrayMember(&element));

  VpiObject struct_net;
  struct_net.type = vpiStructNet;
  element.parent = &struct_net;
  EXPECT_FALSE(VpiNetIsArrayMember(&element));

  element.parent = nullptr;
  EXPECT_FALSE(VpiNetIsArrayMember(&element));
  EXPECT_FALSE(VpiNetIsArrayMember(nullptr));
}

// D2: vpiPackedArrayMember is TRUE for a packed struct/union net, an enum net,
// or a packed array net whose parent is a packed array net; FALSE otherwise.
TEST(NetModel, PackedArrayMemberReadsPackedArrayNetParent) {
  VpiObject packed_array_net;
  packed_array_net.type = vpiPackedArrayNet;

  VpiObject struct_elem;
  struct_elem.type = vpiStructNet;
  struct_elem.parent = &packed_array_net;
  EXPECT_TRUE(VpiNetIsPackedArrayMember(&struct_elem));

  VpiObject enum_elem;
  enum_elem.type = vpiEnumNet;
  enum_elem.parent = &packed_array_net;
  EXPECT_TRUE(VpiNetIsPackedArrayMember(&enum_elem));

  // A plain logic net element does not qualify, even under a packed array net.
  VpiObject logic_elem;
  logic_elem.type = vpiNet;
  logic_elem.parent = &packed_array_net;
  EXPECT_FALSE(VpiNetIsPackedArrayMember(&logic_elem));

  // The right kind, but the parent is not a packed array net.
  VpiObject array_net;
  array_net.type = vpiNetArray;
  struct_elem.parent = &array_net;
  EXPECT_FALSE(VpiNetIsPackedArrayMember(&struct_elem));
  EXPECT_FALSE(VpiNetIsPackedArrayMember(nullptr));
}

// D3: the net bits of a logic net or a bit net are reachable regardless of
// vector expansion; no other net kind exposes net bits this way.
TEST(NetModel, NetBitsAvailableForLogicAndBitNets) {
  EXPECT_TRUE(VpiNetBitIteratorApplies(vpiNet));
  EXPECT_TRUE(VpiNetBitIteratorApplies(vpiBitNet));
  EXPECT_FALSE(VpiNetBitIteratorApplies(vpiStructNet));
  EXPECT_FALSE(VpiNetBitIteratorApplies(vpiNetArray));
}

// D5: continuous assignments and primitive terminals are reachable only from a
// scalar net or a bit-select.
TEST(NetModel, TerminalAccessRequiresScalarNetOrBitSelect) {
  EXPECT_TRUE(VpiNetTerminalAccessAllowed(true));
  EXPECT_FALSE(VpiNetTerminalAccessAllowed(false));
}

// D6: vpiPorts hands back the matching port bits for a net bit reference, and a
// handle to the entire port for an entire net or array net reference.
TEST(NetModel, PortsGranularityByReferenceKind) {
  EXPECT_EQ(VpiPortsReferenceGranularity(vpiNetBit),
            VpiPortGranularity::kPortBits);
  EXPECT_EQ(VpiPortsReferenceGranularity(vpiNet),
            VpiPortGranularity::kEntirePort);
  EXPECT_EQ(VpiPortsReferenceGranularity(vpiNetArray),
            VpiPortGranularity::kEntirePort);
}

// D7: vpiPortInst hands back port bits / scalar ports for a bit or scalar
// reference, unless the highconn is a complex expression whose bit index cannot
// be determined (then the whole port); an entire net or array net reference
// always yields the whole port.
TEST(NetModel, PortInstGranularityByReferenceAndHighconn) {
  // Bit/scalar reference, determinable highconn -> port bits / scalar ports.
  EXPECT_EQ(VpiPortInstReferenceGranularity(
                /*ref_is_bit_or_scalar=*/true,
                /*ref_is_entire_net_or_array=*/false,
                /*highconn_bit_index_undeterminable=*/false),
            VpiPortGranularity::kPortBits);
  // Bit/scalar reference, complex highconn -> the whole port.
  EXPECT_EQ(VpiPortInstReferenceGranularity(true, false, true),
            VpiPortGranularity::kEntirePort);
  // Entire net or array net reference -> the whole port regardless of highconn.
  EXPECT_EQ(VpiPortInstReferenceGranularity(false, true, false),
            VpiPortGranularity::kEntirePort);
  EXPECT_EQ(VpiPortInstReferenceGranularity(false, true, true),
            VpiPortGranularity::kEntirePort);
}

// D8: a vpiPortInst reference inside the highconn but connected to none of the
// port's bits (e.g. a size mismatch) does not qualify as a member.
TEST(NetModel, PortInstMemberQualification) {
  EXPECT_TRUE(VpiPortInstReferenceQualifies(true));
  EXPECT_FALSE(VpiPortInstReferenceQualifies(false));
}

// D9: an implicit net reports vpiLineNo 0 and the vpiImplicitDecl property
// TRUE; an explicitly declared net reports its declared line and FALSE. The
// property is observed through the public vpi_get entry point.
class NetContext : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(NetContext, ImplicitNetDeclarationAndLineNumber) {
  VpiObject implicit_net;
  implicit_net.type = vpiNet;
  implicit_net.implicit_decl = true;
  EXPECT_EQ(vpi_get(vpiImplicitDecl, &implicit_net), 1);
  EXPECT_EQ(VpiNetLineNo(true, 42), 0);

  VpiObject explicit_net;
  explicit_net.type = vpiNet;
  EXPECT_EQ(vpi_get(vpiImplicitDecl, &explicit_net), 0);
  EXPECT_EQ(VpiNetLineNo(false, 42), 42);
}

// D10: vpi_handle(vpiIndex, net_bit) returns the net bit's single index;
// vpi_iterate(vpiIndex, net_bit) over a multidimensional net array bit-select
// returns the indices from the net bit's index outward.
TEST(NetModel, NetBitIndexAndMultidimIndices) {
  VpiObject i0, i1, i2;
  EXPECT_EQ(VpiNetBitIndex({&i0, &i1, &i2}), &i0);
  EXPECT_EQ(VpiNetBitIndex({}), nullptr);

  std::vector<VpiHandle> outward = VpiNetBitIndicesOutward({&i0, &i1, &i2});
  ASSERT_EQ(outward.size(), 3u);
  EXPECT_EQ(outward[0], &i0);
  EXPECT_EQ(outward[2], &i2);
}

// D11: vpiNetType is vpiNettypeNet for a net not declared with a nettype and
// vpiNettypeNetSelect for a select of a nettype net; driver iteration is not
// supported for a vpiNettypeNetSelect.
TEST(NetModel, NettypeValueAndDriverIterationGate) {
  EXPECT_EQ(VpiNetNettypeValue(false), vpiNettypeNet);
  EXPECT_EQ(VpiNetNettypeValue(true), vpiNettypeNetSelect);

  EXPECT_TRUE(VpiNetDriverIterationSupported(vpiNettypeNet));
  EXPECT_FALSE(VpiNetDriverIterationSupported(vpiNettypeNetSelect));
}

// D12: vpiNetType for an interconnect net is vpiInterconnect;
// vpiResolvedNetType for a simulated interconnect net is the resolved type of
// the simulated net.
TEST(NetModel, InterconnectNetTypeAndResolvedType) {
  EXPECT_EQ(VpiInterconnectNetType(), vpiInterconnect);
  EXPECT_EQ(VpiInterconnectResolvedNetType(vpiWand), vpiWand);
  EXPECT_EQ(VpiInterconnectResolvedNetType(vpiTri), vpiTri);
}

// D13: vpiTypespec returns NULL for an interconnect array; for any other net it
// is the net's typespec child.
TEST(NetModel, TypespecNullForInterconnectArray) {
  VpiObject typespec;
  typespec.type = vpiTypespec;

  VpiObject net;
  net.type = vpiNet;
  net.children.push_back(&typespec);
  EXPECT_EQ(VpiNetTypespec(&net), &typespec);

  VpiObject interconnect_array;
  interconnect_array.type = vpiInterconnectArray;
  interconnect_array.children.push_back(&typespec);
  EXPECT_EQ(VpiNetTypespec(&interconnect_array), nullptr);
}

// D21: vpiExpanded on a net bit reports the value of the property for its
// parent net (a scalared/default net is expanded; a vectored net is not),
// observed through the public vpi_get entry point.
TEST_F(NetContext, ExpandedOnNetBitReadsParentNet) {
  VpiObject vectored_net;
  vectored_net.type = vpiNet;
  vectored_net.is_vectored = true;  // a vectored net is reported unexpanded
  VpiObject bit_of_vectored;
  bit_of_vectored.type = vpiNetBit;
  bit_of_vectored.parent = &vectored_net;
  EXPECT_EQ(vpi_get(vpiExpanded, &bit_of_vectored), 0);

  VpiObject plain_net;
  plain_net.type = vpiNet;  // neither vectored nor scalared -> expanded
  VpiObject bit_of_plain;
  bit_of_plain.type = vpiNetBit;
  bit_of_plain.parent = &plain_net;
  EXPECT_EQ(vpi_get(vpiExpanded, &bit_of_plain), 1);
}

// D23: vpiConstantSelect is TRUE for a net with no parent, or for a select with
// all-constant indices over static-bound elements; FALSE otherwise (see A.8.4).
TEST(NetModel, ConstantSelectRule) {
  // No parent -> constant select regardless of the select inputs.
  EXPECT_TRUE(VpiNetConstantSelect(/*has_parent=*/false, false, false));
  // Has parent: TRUE only when both select conditions hold.
  EXPECT_TRUE(VpiNetConstantSelect(true, true, true));
  EXPECT_FALSE(VpiNetConstantSelect(true, true, false));
  EXPECT_FALSE(VpiNetConstantSelect(true, false, true));
}

// D24: vpiSize is the element count for an interconnect array or array net, the
// connected net's size for an interconnect net, the bit width for an integral
// net, the member count for an unpacked struct/union net, and 1 for a net bit.
TEST(NetModel, SizeByNetKind) {
  VpiNetSizeQuery q;

  q = {};
  q.net_type = vpiInterconnectArray;
  q.interconnect_array_count = 8;
  EXPECT_EQ(VpiNetSize(q), 8);

  q = {};
  q.net_type = vpiInterconnectNet;
  q.connected_net_size = 5;
  EXPECT_EQ(VpiNetSize(q), 5);

  q = {};
  q.net_type = vpiNetArray;
  q.array_element_count = 4;
  EXPECT_EQ(VpiNetSize(q), 4);

  q = {};
  q.net_type = vpiIntegerNet;
  q.bit_width = 32;
  EXPECT_EQ(VpiNetSize(q), 32);

  q = {};
  q.net_type = vpiNetBit;
  EXPECT_EQ(VpiNetSize(q), 1);

  // A packed struct net is integral (size in bits); an unpacked one reports its
  // member count.
  q = {};
  q.net_type = vpiStructNet;
  q.packed = true;
  q.bit_width = 12;
  q.member_count = 3;
  EXPECT_EQ(VpiNetSize(q), 12);
  q.packed = false;
  EXPECT_EQ(VpiNetSize(q), 3);

  // The same packed/unpacked split applies to a union net.
  q = {};
  q.net_type = vpiUnionNet;
  q.packed = true;
  q.bit_width = 7;
  q.member_count = 2;
  EXPECT_EQ(VpiNetSize(q), 7);
  q.packed = false;
  EXPECT_EQ(VpiNetSize(q), 2);

  // Edge: vpiSize is undefined for a net that is not one of the above kinds and
  // is not of an integral data type (a real net), reported as 0.
  q = {};
  q.net_type = vpiRealNet;
  q.bit_width = 64;
  EXPECT_EQ(VpiNetSize(q), 0);
}

// D25: vpi_iterate(vpiIndex, net) returns the indices from the net's index
// outward only when the net is an element of an array net; otherwise none.
TEST(NetModel, IndexIterationOnlyForArrayNetElement) {
  VpiObject i0, i1;
  std::vector<VpiHandle> indices = {&i0, &i1};

  std::vector<VpiHandle> member = VpiNetIndicesOutward(true, indices);
  ASSERT_EQ(member.size(), 2u);
  EXPECT_EQ(member[0], &i0);

  EXPECT_TRUE(VpiNetIndicesOutward(false, indices).empty());
}

// D26 (woven with §37.22): vpiRange returns one range per declared dimension,
// dropping implicit element ranges; vpiLeftRange/vpiRightRange report the
// bounds of the leftmost dimension, or NULL when there is none.
TEST(NetModel, RangeIterationAndLeftRightRange) {
  VpiObject lo, hi;

  VpiArrayDimension packed;
  packed.kind = VpiDimensionKind::kPacked;
  packed.left_expr = &hi;
  packed.right_expr = &lo;
  packed.size = 4;

  VpiArrayDimension implicit_elem;
  implicit_elem.kind = VpiDimensionKind::kPacked;
  implicit_elem.implicit_element_range = true;

  std::vector<VpiArrayDimension> dims = {packed, implicit_elem};
  std::vector<VpiRangeDesc> ranges = VpiNetRanges(dims);
  ASSERT_EQ(ranges.size(), 1u);  // the implicit element range is dropped
  EXPECT_EQ(ranges[0].size, 4);

  EXPECT_EQ(VpiNetLeftRange(dims), &hi);
  EXPECT_EQ(VpiNetRightRange(dims), &lo);

  // No dimensions -> the leftmost range is empty, so both relations are NULL.
  EXPECT_EQ(VpiNetLeftRange({}), nullptr);
  EXPECT_EQ(VpiNetRightRange({}), nullptr);
}

// D27 and D29: vpi_get_str(vpiType) reports a permitted spelling of the type
// constant. Because vpiArrayNet aliases vpiNetArray and vpiLogicNet aliases
// vpiNet, either spelling is acceptable; the simulator returns the IEEE 1364
// names. Driven through the public vpi_get_str entry point.
TEST_F(NetContext, TypeStringForAliasedNetKinds) {
  EXPECT_EQ(vpiLogicNet, vpiNet);       // #defined the same (D29)
  EXPECT_EQ(vpiArrayNet, vpiNetArray);  // #defined the same (D27)

  VpiObject logic_net;
  logic_net.type = vpiNet;
  EXPECT_EQ(std::string(vpi_get_str(vpiType, &logic_net)), "vpiNet");

  VpiObject array_net;
  array_net.type = vpiNetArray;
  EXPECT_EQ(std::string(vpi_get_str(vpiType, &array_net)), "vpiNetArray");

  VpiObject struct_net;
  struct_net.type = vpiStructNet;
  EXPECT_EQ(std::string(vpi_get_str(vpiType, &struct_net)), "vpiStructNet");
}

// D28: a bit/logic net with no packed dimension and a net bit are scalars; an
// integral net is a vector; an enum net and an array net defer to their base
// type and element respectively.
TEST(NetModel, ScalarAndVectorRules) {
  VpiNetScalarVectorQuery q;

  // Logic net, no packed dimension -> scalar, not vector.
  q = {};
  q.net_type = vpiNet;
  EXPECT_TRUE(VpiNetScalar(q));
  EXPECT_FALSE(VpiNetVector(q));
  // With a packed dimension it becomes a vector.
  q.has_packed_dimension = true;
  EXPECT_FALSE(VpiNetScalar(q));
  EXPECT_TRUE(VpiNetVector(q));

  // A net bit is a scalar.
  q = {};
  q.net_type = vpiNetBit;
  EXPECT_TRUE(VpiNetScalar(q));
  EXPECT_FALSE(VpiNetVector(q));

  // An integer net is a vector, not a scalar.
  q = {};
  q.net_type = vpiIntegerNet;
  EXPECT_FALSE(VpiNetScalar(q));
  EXPECT_TRUE(VpiNetVector(q));

  // An enum net defers to its base typespec.
  q = {};
  q.net_type = vpiEnumNet;
  q.base_is_vector = true;
  EXPECT_TRUE(VpiNetVector(q));
  EXPECT_FALSE(VpiNetScalar(q));

  // An array net defers to an element.
  q = {};
  q.net_type = vpiNetArray;
  q.element_is_scalar = true;
  EXPECT_TRUE(VpiNetScalar(q));
  EXPECT_FALSE(VpiNetVector(q));

  // A packed struct/union net is integral, so it is a vector (not a scalar); an
  // unpacked one is neither.
  q = {};
  q.net_type = vpiUnionNet;
  q.packed = true;
  EXPECT_TRUE(VpiNetVector(q));
  EXPECT_FALSE(VpiNetScalar(q));
  q.packed = false;
  EXPECT_FALSE(VpiNetVector(q));
  EXPECT_FALSE(VpiNetScalar(q));

  // Edge: for every other net object both properties are FALSE (a real net).
  q = {};
  q.net_type = vpiRealNet;
  EXPECT_FALSE(VpiNetScalar(q));
  EXPECT_FALSE(VpiNetVector(q));
}

// D30: array nets, unpacked struct/union nets, and interconnect arrays have no
// value property; other nets do.
TEST(NetModel, ValuePropertyAvailability) {
  EXPECT_FALSE(VpiNetHasValueProperty(vpiNetArray, false));
  EXPECT_FALSE(VpiNetHasValueProperty(vpiInterconnectArray, false));
  EXPECT_FALSE(
      VpiNetHasValueProperty(vpiStructNet, /*packed_struct_union=*/false));
  EXPECT_TRUE(
      VpiNetHasValueProperty(vpiStructNet, /*packed_struct_union=*/true));
  EXPECT_TRUE(VpiNetHasValueProperty(vpiNet, false));
  EXPECT_TRUE(VpiNetHasValueProperty(vpiBitNet, false));
}

// D31: vpiParent returns the first qualifying prefix object, scanning rightmost
// to leftmost; NULL when none qualifies.
TEST(NetModel, ParentReturnsFirstQualifyingPrefix) {
  VpiObject struct_net, array_net;
  std::vector<VpiParentPrefix> prefixes = {
      {/*qualifies=*/false, nullptr},
      {/*qualifies=*/true, &struct_net},
      {/*qualifies=*/true, &array_net},
  };
  EXPECT_EQ(VpiNetParent(prefixes), &struct_net);

  std::vector<VpiParentPrefix> none = {{false, nullptr}, {false, nullptr}};
  EXPECT_EQ(VpiNetParent(none), nullptr);
}

// D32: vpiElement iterates the subelements of a packed array net (one dimension
// at a time); no other net kind has a vpiElement iteration.
TEST(NetModel, ElementIterationForPackedArrayNet) {
  EXPECT_TRUE(VpiNetElementIteratorApplies(vpiPackedArrayNet));
  EXPECT_FALSE(VpiNetElementIteratorApplies(vpiNetArray));

  VpiObject e0, e1;
  VpiObject packed_array_net;
  packed_array_net.type = vpiPackedArrayNet;
  packed_array_net.children = {&e0, &e1};
  std::vector<VpiHandle> elems = VpiPackedArrayNetElements(&packed_array_net);
  ASSERT_EQ(elems.size(), 2u);
  EXPECT_EQ(elems[0], &e0);

  VpiObject plain_net;
  plain_net.type = vpiNet;
  plain_net.children = {&e0};
  EXPECT_TRUE(VpiPackedArrayNetElements(&plain_net).empty());
}

// D33: vpiStructUnionMember is TRUE for a net or array net whose parent is a
// struct/union net, FALSE otherwise, and is reported FALSE for a net bit.
TEST(NetModel, StructUnionMemberRule) {
  VpiObject struct_net;
  struct_net.type = vpiStructNet;

  VpiObject member_net;
  member_net.type = vpiNet;
  member_net.parent = &struct_net;
  EXPECT_TRUE(VpiNetStructUnionMember(&member_net));

  VpiObject member_array;
  member_array.type = vpiNetArray;
  member_array.parent = &struct_net;
  EXPECT_TRUE(VpiNetStructUnionMember(&member_array));

  // A union net parent also makes the member a struct/union member.
  VpiObject union_net;
  union_net.type = vpiUnionNet;
  VpiObject union_member;
  union_member.type = vpiNet;
  union_member.parent = &union_net;
  EXPECT_TRUE(VpiNetStructUnionMember(&union_member));

  // A net bit's parent is a net, so the property is reported FALSE for it.
  VpiObject net_bit;
  net_bit.type = vpiNetBit;
  net_bit.parent = &struct_net;
  EXPECT_FALSE(VpiNetStructUnionMember(&net_bit));

  // A net whose parent is not a struct/union net.
  VpiObject array_net;
  array_net.type = vpiNetArray;
  member_net.parent = &array_net;
  EXPECT_FALSE(VpiNetStructUnionMember(&member_net));
}

// D34: for a net that is a member of a struct/union, vpiFullName and
// vpiDecompile include the struct-name prefix while vpiName does not.
TEST(NetModel, MemberNetNameForms) {
  VpiVariableNameParts parts;
  parts.top_scope = "top";
  parts.member_prefixes = {"str1"};
  parts.member = "vec";
  parts.index_suffix = "[5]";

  EXPECT_EQ(VpiNetName(parts), "vec[5]");
  EXPECT_EQ(VpiNetDecompile(parts), "str1.vec[5]");
  EXPECT_EQ(VpiNetFullName(parts), "top.str1.vec[5]");
}

}  // namespace
}  // namespace delta
