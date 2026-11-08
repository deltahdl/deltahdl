#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/net.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(NetModel, ArrayNetAndPackedArrayNetClassification) {
  EXPECT_TRUE(VpiIsArrayNet(1));
  EXPECT_TRUE(VpiIsArrayNet(2));
  EXPECT_FALSE(VpiIsArrayNet(0));

  EXPECT_TRUE(VpiIsPackedArrayNet(vpiStructNet, 1));
  EXPECT_TRUE(VpiIsPackedArrayNet(vpiUnionNet, 2));
  EXPECT_TRUE(VpiIsPackedArrayNet(vpiEnumNet, 1));
  EXPECT_FALSE(VpiIsPackedArrayNet(vpiStructNet, 0));
  EXPECT_FALSE(VpiIsPackedArrayNet(vpiNet, 1));
}

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

  VpiObject union_elem;
  union_elem.type = vpiUnionNet;
  union_elem.parent = &packed_array_net;
  EXPECT_TRUE(VpiNetIsPackedArrayMember(&union_elem));

  VpiObject packed_array_elem;
  packed_array_elem.type = vpiPackedArrayNet;
  packed_array_elem.parent = &packed_array_net;
  EXPECT_TRUE(VpiNetIsPackedArrayMember(&packed_array_elem));

  VpiObject logic_elem;
  logic_elem.type = vpiNet;
  logic_elem.parent = &packed_array_net;
  EXPECT_FALSE(VpiNetIsPackedArrayMember(&logic_elem));

  VpiObject array_net;
  array_net.type = vpiNetArray;
  struct_elem.parent = &array_net;
  EXPECT_FALSE(VpiNetIsPackedArrayMember(&struct_elem));
  EXPECT_FALSE(VpiNetIsPackedArrayMember(nullptr));
}

TEST(NetModel, NetBitsAvailableForLogicAndBitNets) {
  EXPECT_TRUE(VpiNetBitIteratorApplies(vpiNet));
  EXPECT_TRUE(VpiNetBitIteratorApplies(vpiBitNet));
  EXPECT_FALSE(VpiNetBitIteratorApplies(vpiStructNet));
  EXPECT_FALSE(VpiNetBitIteratorApplies(vpiNetArray));
}

TEST(NetModel, TerminalAccessRequiresScalarNetOrBitSelect) {
  EXPECT_TRUE(VpiNetTerminalAccessAllowed(true));
  EXPECT_FALSE(VpiNetTerminalAccessAllowed(false));
}

TEST(NetModel, PortsGranularityByReferenceKind) {
  EXPECT_EQ(VpiPortsReferenceGranularity(vpiNetBit),
            VpiPortGranularity::kPortBits);
  EXPECT_EQ(VpiPortsReferenceGranularity(vpiNet),
            VpiPortGranularity::kEntirePort);
  EXPECT_EQ(VpiPortsReferenceGranularity(vpiNetArray),
            VpiPortGranularity::kEntirePort);
}

TEST(NetModel, PortInstGranularityByReferenceAndHighconn) {
  EXPECT_EQ(VpiPortInstReferenceGranularity(true, false, false),
            VpiPortGranularity::kPortBits);
  EXPECT_EQ(VpiPortInstReferenceGranularity(true, false, true),
            VpiPortGranularity::kEntirePort);
  EXPECT_EQ(VpiPortInstReferenceGranularity(false, true, false),
            VpiPortGranularity::kEntirePort);
  EXPECT_EQ(VpiPortInstReferenceGranularity(false, true, true),
            VpiPortGranularity::kEntirePort);
}

TEST(NetModel, PortInstMemberQualification) {
  EXPECT_TRUE(VpiPortInstReferenceQualifies(true));
  EXPECT_FALSE(VpiPortInstReferenceQualifies(false));
}

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
  EXPECT_EQ(vpi_get(vpiImplicitDecl, VpiHandleOf(&implicit_net)), 1);
  EXPECT_EQ(VpiNetLineNo(true, 42), 0);

  implicit_net.file = "first_ref.sv";
  EXPECT_EQ(std::string(vpi_get_str(vpiFile, VpiHandleOf(&implicit_net))),
            "first_ref.sv");

  VpiObject explicit_net;
  explicit_net.type = vpiNet;
  EXPECT_EQ(vpi_get(vpiImplicitDecl, VpiHandleOf(&explicit_net)), 0);
  EXPECT_EQ(VpiNetLineNo(false, 42), 42);
}

TEST(NetModel, NetBitIndexAndMultidimIndices) {
  VpiObject i0, i1, i2;
  EXPECT_EQ(VpiNetBitIndex({&i0, &i1, &i2}), &i0);
  EXPECT_EQ(VpiNetBitIndex({}), nullptr);

  std::vector<VpiHandle> outward = VpiNetBitIndicesOutward({&i0, &i1, &i2});
  ASSERT_EQ(outward.size(), 3u);
  EXPECT_EQ(outward[0], &i0);
  EXPECT_EQ(outward[2], &i2);
}

TEST(NetModel, NettypeValueAndDriverIterationGate) {
  EXPECT_EQ(VpiNetNettypeValue(false), vpiNettypeNet);
  EXPECT_EQ(VpiNetNettypeValue(true), vpiNettypeNetSelect);

  EXPECT_TRUE(VpiNetDriverIterationSupported(vpiNettypeNet));
  EXPECT_FALSE(VpiNetDriverIterationSupported(vpiNettypeNetSelect));
}

TEST_F(NetContext, APartOfANettypeNetIsANettypeNetSelect) {
  Net user;
  user.is_user_nettype = true;
  VpiObject driver;
  driver.type = vpiContAssign;
  VpiObject net;
  net.type = vpiNet;
  net.net = &user;
  net.children.push_back(&driver);
  driver.lhs = &net;
  VpiObject bit;
  bit.type = vpiNetBit;
  bit.parent = &net;
  bit.net = &user;
  bit.children.push_back(&driver);

  EXPECT_EQ(vpi_get(vpiNetType, VpiHandleOf(&net)), vpiNettypeNet);
  EXPECT_EQ(vpi_get(vpiNetType, VpiHandleOf(&bit)), vpiNettypeNetSelect);
  const char* name = vpi_get_str(vpiNetType, VpiHandleOf(&bit));
  ASSERT_NE(name, nullptr);
  EXPECT_EQ(std::string(name), "vpiNettypeNetSelect");
  EXPECT_EQ(vpi_iterate(vpiDriver, VpiHandleOf(&bit)), nullptr);
  EXPECT_EQ(vpi_iterate(vpiLocalDriver, VpiHandleOf(&bit)), nullptr);
  EXPECT_NE(vpi_iterate(vpiDriver, VpiHandleOf(&net)), nullptr);
}

TEST(NetModel, InterconnectNetTypeAndResolvedType) {
  EXPECT_EQ(VpiInterconnectNetType(), vpiInterconnect);
  EXPECT_EQ(VpiInterconnectResolvedNetType(vpiWand), vpiWand);
  EXPECT_EQ(VpiInterconnectResolvedNetType(vpiTri), vpiTri);
}

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

TEST_F(NetContext, ExpandedOnNetBitReadsParentNet) {
  VpiObject vectored_net;
  vectored_net.type = vpiNet;
  vectored_net.is_vectored = true;
  VpiObject bit_of_vectored;
  bit_of_vectored.type = vpiNetBit;
  bit_of_vectored.parent = &vectored_net;
  EXPECT_EQ(vpi_get(vpiExpanded, VpiHandleOf(&bit_of_vectored)), 0);

  VpiObject plain_net;
  plain_net.type = vpiNet;
  VpiObject bit_of_plain;
  bit_of_plain.type = vpiNetBit;
  bit_of_plain.parent = &plain_net;
  EXPECT_EQ(vpi_get(vpiExpanded, VpiHandleOf(&bit_of_plain)), 1);
}

TEST(NetModel, ConstantSelectRule) {
  EXPECT_TRUE(VpiNetConstantSelect(false, false, false));
  EXPECT_TRUE(VpiNetConstantSelect(true, true, true));
  EXPECT_FALSE(VpiNetConstantSelect(true, true, false));
  EXPECT_FALSE(VpiNetConstantSelect(true, false, true));
}

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
  q.net_type = vpiNet;
  q.bit_width = 8;
  EXPECT_EQ(VpiNetSize(q), 8);

  q = {};
  q.net_type = vpiBitNet;
  q.bit_width = 3;
  EXPECT_EQ(VpiNetSize(q), 3);

  q = {};
  q.net_type = vpiEnumNet;
  q.bit_width = 2;
  EXPECT_EQ(VpiNetSize(q), 2);

  q = {};
  q.net_type = vpiNetBit;
  EXPECT_EQ(VpiNetSize(q), 1);

  q = {};
  q.net_type = vpiStructNet;
  q.packed = true;
  q.bit_width = 12;
  q.member_count = 3;
  EXPECT_EQ(VpiNetSize(q), 12);
  q.packed = false;
  EXPECT_EQ(VpiNetSize(q), 3);

  q = {};
  q.net_type = vpiUnionNet;
  q.packed = true;
  q.bit_width = 7;
  q.member_count = 2;
  EXPECT_EQ(VpiNetSize(q), 7);
  q.packed = false;
  EXPECT_EQ(VpiNetSize(q), 2);

  q = {};
  q.net_type = vpiRealNet;
  q.bit_width = 64;
  EXPECT_EQ(VpiNetSize(q), 0);
}

TEST(NetModel, IndexIterationOnlyForArrayNetElement) {
  VpiObject i0, i1;
  std::vector<VpiHandle> indices = {&i0, &i1};

  std::vector<VpiHandle> member = VpiNetIndicesOutward(true, indices);
  ASSERT_EQ(member.size(), 2u);
  EXPECT_EQ(member[0], &i0);

  EXPECT_TRUE(VpiNetIndicesOutward(false, indices).empty());
}

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
  ASSERT_EQ(ranges.size(), 1u);
  EXPECT_EQ(ranges[0].size, 4);

  EXPECT_EQ(VpiNetLeftRange(dims), &hi);
  EXPECT_EQ(VpiNetRightRange(dims), &lo);

  EXPECT_EQ(VpiNetLeftRange({}), nullptr);
  EXPECT_EQ(VpiNetRightRange({}), nullptr);
}

TEST_F(NetContext, TypeStringForAliasedNetKinds) {
  EXPECT_EQ(vpiLogicNet, vpiNet);
  EXPECT_EQ(vpiArrayNet, vpiNetArray);

  VpiObject logic_net;
  logic_net.type = vpiNet;
  EXPECT_EQ(std::string(vpi_get_str(vpiType, VpiHandleOf(&logic_net))),
            "vpiNet");

  VpiObject array_net;
  array_net.type = vpiNetArray;
  EXPECT_EQ(std::string(vpi_get_str(vpiType, VpiHandleOf(&array_net))),
            "vpiNetArray");

  VpiObject struct_net;
  struct_net.type = vpiStructNet;
  EXPECT_EQ(std::string(vpi_get_str(vpiType, VpiHandleOf(&struct_net))),
            "vpiStructNet");
}

TEST(NetModel, ScalarAndVectorRules) {
  VpiNetScalarVectorQuery q;

  q = {};
  q.net_type = vpiNet;
  EXPECT_TRUE(VpiNetScalar(q));
  EXPECT_FALSE(VpiNetVector(q));
  q.has_packed_dimension = true;
  EXPECT_FALSE(VpiNetScalar(q));
  EXPECT_TRUE(VpiNetVector(q));

  q = {};
  q.net_type = vpiBitNet;
  EXPECT_TRUE(VpiNetScalar(q));
  EXPECT_FALSE(VpiNetVector(q));
  q.has_packed_dimension = true;
  EXPECT_FALSE(VpiNetScalar(q));
  EXPECT_TRUE(VpiNetVector(q));

  q = {};
  q.net_type = vpiNetBit;
  EXPECT_TRUE(VpiNetScalar(q));
  EXPECT_FALSE(VpiNetVector(q));

  q = {};
  q.net_type = vpiIntegerNet;
  EXPECT_FALSE(VpiNetScalar(q));
  EXPECT_TRUE(VpiNetVector(q));

  q = {};
  q.net_type = vpiEnumNet;
  q.base_is_vector = true;
  EXPECT_TRUE(VpiNetVector(q));
  EXPECT_FALSE(VpiNetScalar(q));
  q = {};
  q.net_type = vpiEnumNet;
  q.base_is_scalar = true;
  EXPECT_TRUE(VpiNetScalar(q));
  EXPECT_FALSE(VpiNetVector(q));

  q = {};
  q.net_type = vpiNetArray;
  q.element_is_scalar = true;
  EXPECT_TRUE(VpiNetScalar(q));
  EXPECT_FALSE(VpiNetVector(q));
  q = {};
  q.net_type = vpiNetArray;
  q.element_is_vector = true;
  EXPECT_TRUE(VpiNetVector(q));
  EXPECT_FALSE(VpiNetScalar(q));

  q = {};
  q.net_type = vpiStructNet;
  q.packed = true;
  EXPECT_TRUE(VpiNetVector(q));
  EXPECT_FALSE(VpiNetScalar(q));

  q = {};
  q.net_type = vpiUnionNet;
  q.packed = true;
  EXPECT_TRUE(VpiNetVector(q));
  EXPECT_FALSE(VpiNetScalar(q));
  q.packed = false;
  EXPECT_FALSE(VpiNetVector(q));
  EXPECT_FALSE(VpiNetScalar(q));

  q = {};
  q.net_type = vpiRealNet;
  EXPECT_FALSE(VpiNetScalar(q));
  EXPECT_FALSE(VpiNetVector(q));
}

TEST(NetModel, ValuePropertyAvailability) {
  EXPECT_FALSE(VpiNetHasValueProperty(vpiNetArray, false));
  EXPECT_FALSE(VpiNetHasValueProperty(vpiInterconnectArray, false));
  EXPECT_FALSE(VpiNetHasValueProperty(vpiStructNet, false));
  EXPECT_TRUE(VpiNetHasValueProperty(vpiStructNet, true));
  EXPECT_FALSE(VpiNetHasValueProperty(vpiUnionNet, false));
  EXPECT_TRUE(VpiNetHasValueProperty(vpiUnionNet, true));
  EXPECT_TRUE(VpiNetHasValueProperty(vpiNet, false));
  EXPECT_TRUE(VpiNetHasValueProperty(vpiBitNet, false));
}

TEST(NetModel, ParentReturnsFirstQualifyingPrefix) {
  VpiObject struct_net, array_net;
  std::vector<VpiParentPrefix> prefixes = {
      {false, nullptr},
      {true, &struct_net},
      {true, &array_net},
  };
  EXPECT_EQ(VpiNetParent(prefixes), &struct_net);

  std::vector<VpiParentPrefix> none = {{false, nullptr}, {false, nullptr}};
  EXPECT_EQ(VpiNetParent(none), nullptr);
}

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

  VpiObject union_net;
  union_net.type = vpiUnionNet;
  VpiObject union_member;
  union_member.type = vpiNet;
  union_member.parent = &union_net;
  EXPECT_TRUE(VpiNetStructUnionMember(&union_member));

  VpiObject net_bit;
  net_bit.type = vpiNetBit;
  net_bit.parent = &struct_net;
  EXPECT_FALSE(VpiNetStructUnionMember(&net_bit));

  VpiObject array_net;
  array_net.type = vpiNetArray;
  member_net.parent = &array_net;
  EXPECT_FALSE(VpiNetStructUnionMember(&member_net));
}

TEST(NetModel, MemberNetNameForms) {
  VpiVariableNameParts parts;
  parts.top_scope = "top";
  parts.member_prefixes = {"str1"};
  parts.member = "vec";
  parts.index_suffix = "[5]";

  EXPECT_EQ(VpiNetName(parts), "vec[5]");
  EXPECT_EQ(VpiNetDecompile(parts), "str1.vec[5]");
  EXPECT_EQ(VpiNetFullName(parts), "top.str1.vec[5]");

  VpiVariableNameParts top_level;
  top_level.top_scope = "top";
  top_level.member = "warr1";
  top_level.index_suffix = "[1][9]";
  EXPECT_EQ(VpiNetName(top_level), "warr1[1][9]");
  EXPECT_EQ(VpiNetDecompile(top_level), "warr1[1][9]");
  EXPECT_EQ(VpiNetFullName(top_level), "top.warr1[1][9]");

  VpiVariableNameParts nested;
  nested.top_scope = "top";
  nested.member_prefixes = {"str1", "inner1"};
  nested.member = "j1";
  EXPECT_EQ(VpiNetName(nested), "j1");
  EXPECT_EQ(VpiNetDecompile(nested), "str1.inner1.j1");
  EXPECT_EQ(VpiNetFullName(nested), "top.str1.inner1.j1");

  VpiVariableNameParts no_scope;
  no_scope.member = "w";
  EXPECT_EQ(VpiNetFullName(no_scope), VpiNetDecompile(no_scope));
  EXPECT_EQ(VpiNetFullName(no_scope), "w");
}

class NetBitsOfARun : public VpiDesignRun {
 protected:
  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }

  static int CountOf(int type, vpiHandle ref) {
    int count = 0;
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return 0;
    while (vpi_scan(it) != nullptr) ++count;
    return count;
  }

  static vpiHandle Net() {
    return vpi_handle_by_name(VpiText("top.n"), nullptr);
  }
};

constexpr const char* kVectorNet =
    "module top; wire [3:0] n = 4'b0100; endmodule\n";

TEST_F(NetBitsOfARun, AVectorNetHasOneBitPerBit) {
  Run(kVectorNet);
  EXPECT_EQ(CountOf(vpiBit, Net()), 4);
}

TEST_F(NetBitsOfARun, ANetsBitIsANetBit) {
  Run(kVectorNet);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_index(Net(), 2)), vpiNetBit);
}

TEST_F(NetBitsOfARun, ANetBitHoldsItsBit) {
  Run(kVectorNet);
  EXPECT_EQ(IntOf(vpi_handle_by_index(Net(), 2)), 1);
}

TEST_F(NetBitsOfARun, ANetBitAtAConstantIndexIsAConstantSelect) {
  Run(kVectorNet);
  EXPECT_EQ(vpi_get(vpiConstantSelect, vpi_handle_by_index(Net(), 2)), 1);
}

TEST_F(NetBitsOfARun, ANetWithNoParentIsAConstantSelect) {
  Run(kVectorNet);
  EXPECT_EQ(vpi_get(vpiConstantSelect, Net()), 1);
}

class NetTypesOfARun : public VpiDesignRun {
 protected:
  static int NetTypeOf(const char* name) {
    return vpi_get(vpiNetType, vpi_handle_by_name(VpiText(name), nullptr));
  }
};

constexpr const char* kNetKinds =
    "module top;\n"
    "  nettype logic mynet;\n"
    "  wire w; tri t; wand wa; supply0 s0; trireg tr; uwire u; mynet n;\n"
    "endmodule\n";

TEST_F(NetTypesOfARun, AWireIsAWire) {
  Run(kNetKinds);
  EXPECT_EQ(NetTypeOf("top.w"), vpiWire);
}

TEST_F(NetTypesOfARun, ATriIsATri) {
  Run(kNetKinds);
  EXPECT_EQ(NetTypeOf("top.t"), vpiTri);
}

TEST_F(NetTypesOfARun, AWandIsAWand) {
  Run(kNetKinds);
  EXPECT_EQ(NetTypeOf("top.wa"), vpiWand);
}

TEST_F(NetTypesOfARun, ASupply0IsASupply0) {
  Run(kNetKinds);
  EXPECT_EQ(NetTypeOf("top.s0"), vpiSupply0);
}

TEST_F(NetTypesOfARun, ATriregIsATriReg) {
  Run(kNetKinds);
  EXPECT_EQ(NetTypeOf("top.tr"), vpiTriReg);
}

TEST_F(NetTypesOfARun, AUwireIsAUwire) {
  Run(kNetKinds);
  EXPECT_EQ(NetTypeOf("top.u"), vpiUwire);
}

TEST_F(NetTypesOfARun, AUserNettypeNetIsANettypeNet) {
  Run(kNetKinds);
  EXPECT_EQ(NetTypeOf("top.n"), vpiNettypeNet);
}

TEST_F(NetTypesOfARun, EveryNetKindReportsItsConstantAndItsName) {
  Run("module top;\n"
      "  nettype logic mynet;\n"
      "  wire w; tri t; tri0 t0; tri1 t1; trireg tr; triand ta; trior to;\n"
      "  wand wa; wor wo; supply0 s0; supply1 s1; uwire u; mynet n;\n"
      "endmodule\n");
  struct Kind {
    const char* net;
    int type;
    const char* name;
  };
  const Kind kKinds[] = {
      {"top.w", vpiWire, "vpiWire"},
      {"top.t", vpiTri, "vpiTri"},
      {"top.t0", vpiTri0, "vpiTri0"},
      {"top.t1", vpiTri1, "vpiTri1"},
      {"top.tr", vpiTriReg, "vpiTriReg"},
      {"top.ta", vpiTriAnd, "vpiTriAnd"},
      {"top.to", vpiTriOr, "vpiTriOr"},
      {"top.wa", vpiWand, "vpiWand"},
      {"top.wo", vpiWor, "vpiWor"},
      {"top.s0", vpiSupply0, "vpiSupply0"},
      {"top.s1", vpiSupply1, "vpiSupply1"},
      {"top.u", vpiUwire, "vpiUwire"},
      {"top.n", vpiNettypeNet, "vpiNettypeNet"},
  };
  for (const Kind& k : kKinds) {
    vpiHandle net = vpi_handle_by_name(VpiText(k.net), nullptr);
    ASSERT_NE(net, nullptr) << k.net;
    EXPECT_EQ(vpi_get(vpiNetType, net), k.type) << k.net;
    const char* name = vpi_get_str(vpiNetType, net);
    ASSERT_NE(name, nullptr) << k.net;
    EXPECT_EQ(std::string(name), k.name);
  }
}

TEST_F(NetTypesOfARun, TheNetTypesNameIsItsConstant) {
  Run(kNetKinds);
  EXPECT_STREQ(
      vpi_get_str(vpiNetType, vpi_handle_by_name(VpiText("top.wa"), nullptr)),
      "vpiWand");
}

TEST_F(NetBitsOfARun, AnOuterPackedSelectOfANetIsANetVector) {
  Run("module top; wire [3:0][7:0] n = 32'h44332211; integer i = 1;\n"
      "  wire [7:0] y; assign y = n[i];\n"
      "endmodule\n");
  vpiHandle y = vpi_handle_by_name(VpiText("top.y"), nullptr);
  vpiHandle it =
      vpi_iterate(vpiContAssign, vpi_handle_by_name(VpiText("top"), nullptr));
  vpiHandle rhs = nullptr;
  while (vpiHandle assign = it == nullptr ? nullptr : vpi_scan(it)) {
    if (VpiObjectOf(vpi_handle(vpiLhs, assign)) == VpiObjectOf(y)) {
      rhs = vpi_handle(vpiRhs, assign);
    }
  }
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(vpi_get(vpiType, rhs), vpiLogicNet);
  EXPECT_EQ(vpi_get(vpiSize, rhs), 8);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, rhs)), VpiObjectOf(Net()));
  EXPECT_EQ(IntOf(rhs), 0x22);
}

TEST(NetModel, AStructNetWithNoParentIsNoPackedArrayMember) {
  VpiObject orphan;
  orphan.type = vpiStructNet;
  EXPECT_FALSE(VpiNetIsPackedArrayMember(&orphan));
}

TEST(NetModel, AnyOtherReferenceSelectsTheWholePort) {
  EXPECT_EQ(VpiPortInstReferenceGranularity(false, false, false),
            VpiPortGranularity::kEntirePort);
}

TEST(NetModel, TheNetTypespecIsFoundAmongOtherChildren) {
  VpiObject bit;
  bit.type = vpiNetBit;
  VpiObject typespec;
  typespec.type = vpiTypespec;
  VpiObject net;
  net.type = vpiNet;
  net.children = {&bit, &typespec};
  EXPECT_EQ(VpiNetTypespec(&net), &typespec);

  net.children = {&bit};
  EXPECT_EQ(VpiNetTypespec(&net), nullptr);
  EXPECT_EQ(VpiNetTypespec(nullptr), nullptr);
}

TEST_F(NetContext, ANetBitWithNoParentIsExpanded) {
  VpiObject bit;
  bit.type = vpiNetBit;
  EXPECT_EQ(vpi_get(vpiExpanded, VpiHandleOf(&bit)), 1);
}

TEST(NetModel, EveryIntegralTypedNetIsAVectorSizedInBits) {
  for (int kind : {vpiIntegerNet, vpiTimeNet, vpiByteNet, vpiShortIntNet,
                   vpiIntNet, vpiLongIntNet, vpiPackedArrayNet}) {
    VpiNetSizeQuery size;
    size.net_type = kind;
    size.bit_width = 13;
    EXPECT_EQ(VpiNetSize(size), 13) << kind;
    VpiNetScalarVectorQuery shape;
    shape.net_type = kind;
    EXPECT_TRUE(VpiNetVector(shape)) << kind;
  }
}

TEST(NetModel, NoHandleHasPackedArrayElements) {
  EXPECT_TRUE(VpiPackedArrayNetElements(nullptr).empty());
}

TEST(NetModel, EveryKindTheNetsClassGroupsIsANet) {
  for (int kind :
       {vpiNet, vpiNetBit, vpiNetArray, vpiStructNet, vpiUnionNet, vpiEnumNet,
        vpiIntegerNet, vpiTimeNet, vpiBitNet, vpiByteNet, vpiShortIntNet,
        vpiIntNet, vpiLongIntNet, vpiRealNet, vpiShortRealNet,
        vpiPackedArrayNet, vpiInterconnectNet, vpiInterconnectArray}) {
    EXPECT_TRUE(VpiIsNetsType(kind)) << kind;
  }
  EXPECT_FALSE(VpiIsNetsType(vpiReg));
}

TEST_F(NetContext, AConstantPackedSelectReachesItsNet) {
  VpiObject net;
  net.type = vpiNet;
  VpiObject slice;
  slice.type = vpiNet;
  slice.bit_offset = 8;
  slice.parent = &net;
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, VpiHandleOf(&slice))), &net);
  VpiObject orphan;
  orphan.type = vpiNet;
  orphan.bit_offset = 8;
  EXPECT_EQ(vpi_handle(vpiParent, VpiHandleOf(&orphan)), nullptr);
}
}  // namespace
}  // namespace delta
