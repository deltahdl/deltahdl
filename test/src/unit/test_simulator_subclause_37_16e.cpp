#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class NetShapesOfARun : public VpiDesignRun {
 protected:
  static std::vector<int> ShapeOf(vpiHandle net) {
    if (net == nullptr) return {};
    return {vpi_get(vpiScalar, net), vpi_get(vpiVector, net)};
  }

  static std::vector<int> KindsReached(int relation, vpiHandle ref) {
    std::vector<int> kinds;
    for (vpiHandle obj : ObjectsOf(relation, ref)) {
      kinds.push_back(vpi_get(vpiType, obj));
    }
    return kinds;
  }

  static vpiHandle IndexOf(vpiHandle ref, const std::vector<int>& indices) {
    for (int index : indices) {
      if (ref == nullptr) return nullptr;
      ref = vpi_handle_by_index(ref, index);
    }
    return ref;
  }

  static VpiObject* ParentOf(vpiHandle obj) {
    return obj == nullptr ? nullptr : VpiObjectOf(vpi_handle(vpiParent, obj));
  }
};

std::vector<int> Scalar() { return {1, 0}; }
std::vector<int> Vector() { return {0, 1}; }
std::vector<int> Neither() { return {0, 0}; }

TEST_F(NetShapesOfARun, AnEnumNetOfOneBitIsAScalar) {
  Run("typedef enum bit {B0, B1} eb_t; nettype eb_t ebn_t;\n"
      "typedef enum logic {L0, L1} el_t;\n"
      "module top; ebn_t eb; wire el_t el; endmodule\n");
  EXPECT_EQ(ShapeOf(By("top.eb")), Scalar());
  EXPECT_EQ(ShapeOf(By("top.el")), Scalar());
}

TEST_F(NetShapesOfARun, AnEnumNetOfAVectorBaseIsAVector) {
  Run("typedef enum logic [1:0] {V0, V1} ev_t;\n"
      "typedef enum int {I0, I1} ei_t; nettype ei_t ein_t;\n"
      "module top; wire ev_t ev; ein_t ei; endmodule\n");
  EXPECT_EQ(ShapeOf(By("top.ev")), Vector());
  EXPECT_EQ(ShapeOf(By("top.ei")), Vector());
}

TEST_F(NetShapesOfARun, DISABLED_AnEnumNetOfAOneBitVectorBaseIsAVector) {
  Run("typedef enum logic [0:0] {O0, O1} eo_t;\n"
      "module top; wire eo_t eo; endmodule\n");
  EXPECT_EQ(ShapeOf(By("top.eo")), Vector());
}

TEST_F(NetShapesOfARun, ABitNetIsAScalarAndABitVectorNetAVector) {
  Run("nettype bit b_t; nettype bit [3:0] bv_t;\n"
      "module top; b_t b; bv_t bv; endmodule\n");
  EXPECT_EQ(ShapeOf(By("top.b")), Scalar());
  EXPECT_EQ(ShapeOf(By("top.bv")), Vector());
}

TEST_F(NetShapesOfARun, PackedStructAndUnionNetsAreVectors) {
  Run("typedef struct packed { logic a; logic [1:0] b; } ps_t;\n"
      "typedef union packed { logic [2:0] x; logic [2:0] y; } pu_t;\n"
      "module top; wire ps_t ps; wire pu_t pu; endmodule\n");
  EXPECT_EQ(ShapeOf(By("top.ps")), Vector());
  EXPECT_EQ(ShapeOf(By("top.pu")), Vector());
}

TEST_F(NetShapesOfARun, RealNetsAreNeitherScalarNorVector) {
  Run("nettype real r_t; nettype shortreal sr_t;\n"
      "module top; r_t r; sr_t sr; endmodule\n");
  EXPECT_EQ(ShapeOf(By("top.r")), Neither());
  EXPECT_EQ(ShapeOf(By("top.sr")), Neither());
}

TEST_F(NetShapesOfARun, AnArrayOfScalarNetsIsAScalar) {
  Run("module top; wire a [0:3]; endmodule\n");
  EXPECT_EQ(ShapeOf(By("top.a")), Scalar());
}

TEST_F(NetShapesOfARun, TheOtherIntegralNetsAreVectors) {
  Run("nettype byte by_t; nettype shortint si_t; nettype int in_t;\n"
      "nettype longint li_t;\n"
      "module top; wire time t; by_t by; si_t si; in_t in; li_t li;\n"
      "  wire logic [1:0][3:0] pa;\n"
      "endmodule\n");
  for (const char* name :
       {"top.t", "top.by", "top.si", "top.in", "top.li", "top.pa"}) {
    EXPECT_EQ(ShapeOf(By(name)), Vector()) << name;
  }
}

TEST_F(NetShapesOfARun, AnUnpackedUnionNetsSizeIsItsMemberCount) {
  Run("typedef union { logic [7:0] a; logic b; logic [3:0] c; } uu_t;\n"
      "module top; wire uu_t uu; endmodule\n");
  EXPECT_EQ(vpi_get(vpiSize, By("top.uu")), 3);
}

TEST_F(NetShapesOfARun, AnInterconnectArraysSizeIsItsElementCount) {
  Run("module top; interconnect ic [0:2]; endmodule\n");
  EXPECT_EQ(vpi_get(vpiSize, By("top.ic")), 3);
}

TEST_F(NetShapesOfARun, DISABLED_AnInterconnectNetsSizeIsItsConnectedNets) {
  Run("module leaf(input wire [4:0] p); endmodule\n"
      "module top; interconnect ic; leaf u(ic); endmodule\n");
  EXPECT_EQ(vpi_get(vpiSize, By("top.ic")), 5);
}

TEST_F(NetShapesOfARun, ANetBitsSizeIsOne) {
  Run("module top; wire [3:0] w; endmodule\n");
  vpiHandle bit = vpi_handle_by_index(By("top.w"), 2);
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(vpi_get(vpiSize, bit), 1);
}

TEST_F(NetShapesOfARun, IntegerIntAndTimeNetsHaveTheirWidths) {
  Run("nettype int in_t;\n"
      "module top; wire integer g; in_t i; wire time t; endmodule\n");
  EXPECT_EQ(vpi_get(vpiSize, By("top.g")), 32);
  EXPECT_EQ(vpi_get(vpiSize, By("top.i")), 32);
  EXPECT_EQ(vpi_get(vpiSize, By("top.t")), 64);
}

TEST_F(NetShapesOfARun, AnInterconnectArrayByNameIsAnInterconnect) {
  Run("module top; interconnect a [0:1]; endmodule\n");
  vpiHandle a = vpi_handle_by_name(VpiText("top.a"), nullptr);
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(vpi_get(vpiNetType, a), vpiInterconnect);
}

std::string PrimTermsDesign() {
  return "module top(input a, output o); wire [1:0] w; wire x;\n"
         "  and g(o, a, w[0]); and h(x, w[0], w[1]);\n"
         "endmodule\n";
}

TEST_F(NetShapesOfARun, DISABLED_AVectorNetHasNoPrimTerms) {
  Run(PrimTermsDesign());
  EXPECT_TRUE(ObjectsOf(vpiPrimTerm, By("top.w")).empty());
}

TEST_F(NetShapesOfARun, AScalarNetReachesItsPrimTerm) {
  Run(PrimTermsDesign());
  vpiHandle a = Named(vpiNet, By("top"), "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(ObjectsOf(vpiPrimTerm, a).size(), 1U);
}

TEST_F(NetShapesOfARun, DISABLED_AVectorNetsBitReachesItsPrimTerms) {
  Run(PrimTermsDesign());
  EXPECT_EQ(ObjectsOf(vpiPrimTerm, IndexOf(By("top.w"), {0})).size(), 2U);
  EXPECT_EQ(ObjectsOf(vpiPrimTerm, IndexOf(By("top.w"), {1})).size(), 1U);
}

TEST_F(NetShapesOfARun, AnArrayNetMemberOfAStructNetIsAStructUnionMember) {
  Run("typedef struct { logic [1:0] arr [0:3]; logic b; } s_t;\n"
      "module top; wire s_t sn; endmodule\n");
  vpiHandle arr = Named(vpiMember, By("top.sn"), "arr");
  ASSERT_NE(arr, nullptr);
  EXPECT_EQ(vpi_get(vpiStructUnionMember, arr), 1);
}

TEST_F(NetShapesOfARun, ArrayElementsAndSubelementsAreNoStructUnionMembers) {
  Run("typedef struct packed { logic a; logic b; } p_t;\n"
      "module top; wire p_t sa [0:1]; wire p_t [1:0] pa; endmodule\n");
  vpiHandle element = IndexOf(By("top.sa"), {1});
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(vpi_get(vpiStructUnionMember, element), 0);
  const std::vector<vpiHandle> kSubs = ObjectsOf(vpiElement, By("top.pa"));
  ASSERT_EQ(kSubs.size(), 2U);
  EXPECT_EQ(vpi_get(vpiStructUnionMember, kSubs[0]), 0);
}

TEST_F(NetShapesOfARun, AnImplicitPortConnectionNetIsAtLineZero) {
  Run("module c(input a); endmodule\n"
      "module top;\n"
      "  c u(.a(n));\n"
      "endmodule\n");
  vpiHandle n = By("top.n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(vpi_get(vpiLineNo, n), 0);
  EXPECT_STREQ(vpi_get_str(vpiFile, n), "<test>");
}

TEST_F(NetShapesOfARun, NamedAndPositionalPortConnectionsDeclareImplicitly) {
  Run("module c(input a); endmodule\n"
      "module top; c u(.a(p)); c v(q); endmodule\n");
  EXPECT_EQ(vpi_get(vpiImplicitDecl, By("top.p")), 1);
  EXPECT_EQ(vpi_get(vpiImplicitDecl, By("top.q")), 1);
}

TEST_F(NetShapesOfARun, AGateTerminalDeclaresImplicitly) {
  Run("module top; wire a; buf b1(o, a); endmodule\n");
  EXPECT_EQ(vpi_get(vpiImplicitDecl, By("top.o")), 1);
  EXPECT_EQ(vpi_get(vpiImplicitDecl, By("top.a")), 0);
}

TEST_F(NetShapesOfARun, BitsOfScalaredAndPlainNetsAreExpanded) {
  Run("module top; wire scalared [3:0] s; wire [3:0] n; endmodule\n");
  vpiHandle s2 = IndexOf(By("top.s"), {2});
  vpiHandle n2 = IndexOf(By("top.n"), {2});
  ASSERT_NE(s2, nullptr);
  ASSERT_NE(n2, nullptr);
  EXPECT_EQ(vpi_get(vpiExpanded, s2), 1);
  EXPECT_EQ(vpi_get(vpiExpanded, n2), 1);
}

TEST_F(NetShapesOfARun,
       DISABLED_ABitOfAnArrayNetElementHasThePackedElementAsParent) {
  Run("module top; wire logic [1:0][2:3] mda [4:6][7:8]; endmodule\n");
  vpiHandle mda = By("top.mda");
  vpiHandle element = IndexOf(mda, {6, 8});
  ASSERT_NE(element, nullptr);
  vpiHandle bit = IndexOf(element, {1, 3});
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(ParentOf(bit), VpiObjectOf(element));
  EXPECT_EQ(ParentOf(IndexOf(element, {1})), VpiObjectOf(element));
  EXPECT_EQ(ParentOf(element), VpiObjectOf(mda));
}

TEST_F(NetShapesOfARun, DISABLED_AStructMembersBitsChainUpToTheUnpackedArray) {
  Run("module top;\n"
      "  wire struct { integer i1; logic [1:0][2:3] bvec [4:5]; } spa "
      "[9:11][12:13];\n"
      "endmodule\n");
  vpiHandle spa = By("top.spa");
  vpiHandle element = IndexOf(spa, {9, 12});
  ASSERT_NE(element, nullptr);
  vpiHandle bvec = Named(vpiMember, element, "bvec");
  ASSERT_NE(bvec, nullptr);
  vpiHandle bvec4 = IndexOf(bvec, {4});
  vpiHandle bit = IndexOf(bvec4, {0});
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(ParentOf(bit), VpiObjectOf(bvec4));
  EXPECT_EQ(ParentOf(bvec4), VpiObjectOf(bvec));
  EXPECT_EQ(ParentOf(bvec), VpiObjectOf(element));
  EXPECT_EQ(ParentOf(element), VpiObjectOf(spa));
  EXPECT_EQ(ParentOf(spa), nullptr);
}

TEST_F(NetShapesOfARun, ATopLevelNetHasNoParent) {
  Run("module top; wire [3:0] w; endmodule\n");
  EXPECT_EQ(ParentOf(By("top.w")), nullptr);
}

std::string NamesDesign() {
  return "module top;\n"
         "  wire [7:0] warr1 [1:4][9:15];\n"
         "  wire struct {\n"
         "    integer i1; logic [1:4] vec [5:8];\n"
         "    struct { time t1; integer j1; } inner1;\n"
         "  } str1;\n"
         "endmodule\n";
}

TEST_F(NetShapesOfARun, ATwoDimensionalElementKeepsBothIndicesInItsNames) {
  Run(NamesDesign());
  vpiHandle element = IndexOf(By("top.warr1"), {1, 9});
  ASSERT_NE(element, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, element), "top.warr1[1][9]");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, element), "warr1[1][9]");
  EXPECT_STREQ(vpi_get_str(vpiName, element), "warr1[1][9]");
}

TEST_F(NetShapesOfARun, DISABLED_AMemberThroughAnUnpackedArrayKeepsItsIndex) {
  Run(NamesDesign());
  vpiHandle vec = Named(vpiMember, By("top.str1"), "vec");
  ASSERT_NE(vec, nullptr);
  vpiHandle element = IndexOf(vec, {5});
  ASSERT_NE(element, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, element), "top.str1.vec[5]");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, element), "str1.vec[5]");
  EXPECT_STREQ(vpi_get_str(vpiName, element), "vec[5]");
}

TEST_F(NetShapesOfARun, AStructMembersNamesCarryItsPrefixesButItsNameDoesNot) {
  Run(NamesDesign());
  vpiHandle i1 = Named(vpiMember, By("top.str1"), "i1");
  ASSERT_NE(i1, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, i1), "top.str1.i1");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, i1), "str1.i1");
  EXPECT_STREQ(vpi_get_str(vpiName, i1), "i1");
}

TEST_F(NetShapesOfARun, AMemberIsFoundByItsDecompileOrItsFullName) {
  Run(NamesDesign());
  vpiHandle j1 = By("top.str1.inner1.j1");
  ASSERT_NE(j1, nullptr);
  vpiHandle in_scope = vpi_handle_by_name(VpiText("str1.inner1.j1"), By("top"));
  vpiHandle from_top =
      vpi_handle_by_name(VpiText("top.str1.inner1.j1"), nullptr);
  ASSERT_NE(in_scope, nullptr);
  ASSERT_NE(from_top, nullptr);
  EXPECT_EQ(VpiObjectOf(in_scope), VpiObjectOf(j1));
  EXPECT_EQ(VpiObjectOf(from_top), VpiObjectOf(j1));
}

std::string ConnectivityDesign() {
  return "module top; wire [1:0] z; wire [1:0] z2; wire y;\n"
         "  wire [3:0] p; wire [1:0] y2; wire [3:0] q;\n"
         "  assign y = z[0] & z[1];\n"
         "  assign {z2[1], z2[0]} = 2'b01;\n"
         "  assign p[1:0] = 2'b11; assign y2 = p[3:2];\n"
         "  assign q = 4'h1;\n"
         "endmodule\n";
}

TEST_F(NetShapesOfARun, ALoadOrDriverTouchingManyBitsComesBackOnce) {
  Run(ConnectivityDesign());
  for (int relation : {vpiLoad, vpiLocalLoad}) {
    EXPECT_EQ(KindsReached(relation, By("top.z")),
              (std::vector<int>{vpiContAssign}));
  }
  for (int relation : {vpiDriver, vpiLocalDriver}) {
    EXPECT_EQ(KindsReached(relation, By("top.z2")),
              (std::vector<int>{vpiContAssign}));
  }
}

TEST_F(NetShapesOfARun, DISABLED_APartSelectLoadOrDriverIsThePartSelect) {
  Run(ConnectivityDesign());
  for (int relation : {vpiDriver, vpiLocalDriver, vpiLoad, vpiLocalLoad}) {
    EXPECT_EQ(KindsReached(relation, By("top.p")),
              (std::vector<int>{vpiPartSelect}));
  }
}

TEST_F(NetShapesOfARun, ADriverOfEveryBitIsItself) {
  Run(ConnectivityDesign());
  EXPECT_EQ(KindsReached(vpiDriver, By("top.q")),
            (std::vector<int>{vpiContAssign}));
}

TEST_F(NetShapesOfARun, DISABLED_APartSelectPortConnectionIsThePartSelect) {
  Run("module c(input i); endmodule\n"
      "module top; wire [1:0] b; c u(.i(b[1:1])); endmodule\n");
  EXPECT_EQ(KindsReached(vpiLoad, By("top.b")),
            (std::vector<int>{vpiPartSelect}));
}

TEST_F(NetShapesOfARun, DISABLED_ANetsContAssignsAndPrimTermsCrossPorts) {
  Run("module sub(input c, output d); assign d = c; endmodule\n"
      "module gate(input c, output d); buf b(d, c); endmodule\n"
      "module top; wire x, z, gx, gz;\n"
      "  sub u(.c(x), .d(z)); gate g(.c(gx), .d(gz));\n"
      "endmodule\n");
  EXPECT_EQ(ObjectsOf(vpiContAssign, By("top.x")).size(), 1U);
  EXPECT_EQ(ObjectsOf(vpiContAssign, By("top.z")).size(), 1U);
  EXPECT_EQ(ObjectsOf(vpiPrimTerm, By("top.gx")).size(), 1U);
  EXPECT_EQ(ObjectsOf(vpiPrimTerm, By("top.gz")).size(), 1U);
}

}  // namespace
}  // namespace delta
