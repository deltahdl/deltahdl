#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// A design run with a PLI application registered, its nets read back once the
// run is over.
class NetDetailsOfARun : public VpiDesignRun {
 protected:
  // The integer value of an object.
  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }

  // The integer values of the objects of `type` `ref` reaches, in order.
  static std::vector<int> IntsOf(int type, vpiHandle ref) {
    std::vector<int> values;
    for (vpiHandle obj : ObjectsOf(type, ref)) values.push_back(IntOf(obj));
    return values;
  }

  // The bounds of each range `obj` reaches, left then right, in order.
  static std::vector<int> BoundsOf(vpiHandle obj) {
    std::vector<int> bounds;
    for (vpiHandle range : ObjectsOf(vpiRange, obj)) {
      bounds.push_back(IntOf(vpi_handle(vpiLeftRange, range)));
      bounds.push_back(IntOf(vpi_handle(vpiRightRange, range)));
    }
    return bounds;
  }
};

// §37.16 detail 10: a net bit's vpiIndex is its own index, and its vpiIndex
// iteration reaches the index in each dimension that names it, starting with
// its own and working outward. The first bit of w is w[1][2] (#7057).
TEST_F(NetDetailsOfARun, ANetBitReachesItsIndicesWorkingOutward) {
  Run("module top; wire [1:0][2:0] w; endmodule\n");
  const std::vector<vpiHandle> kBits = ObjectsOf(vpiBit, By("top.w"));
  ASSERT_EQ(kBits.size(), 6U);
  EXPECT_EQ(IntOf(vpi_handle(vpiIndex, kBits[0])), 2);
  EXPECT_EQ(IntsOf(vpiIndex, kBits[0]), (std::vector<int>{2, 1}));
  EXPECT_EQ(IntsOf(vpiIndex, kBits[4]), (std::vector<int>{1, 0}));
}

// §37.16 (figure) and detail 25: a net in an array net reaches its index
// through vpiIndex, and its vpiIndex iteration the indices that select it out
// of the array net, its own first and working outward. Its own bits are none
// of them, and a subarray of a multidimensional array net reaches its own
// index alone (#7058); a net in one reaches its indices from every dimension
// (#7394).
TEST_F(NetDetailsOfARun, ANetInAnArrayNetReachesItsIndices) {
  Run("module top; wire [3:0] m [0:2]; wire n [0:2][4:5]; endmodule\n");
  vpiHandle m1 = vpi_handle_by_index(By("top.m"), 1);
  ASSERT_NE(m1, nullptr);
  EXPECT_EQ(IntOf(vpi_handle(vpiIndex, m1)), 1);
  EXPECT_EQ(IntsOf(vpiIndex, m1), (std::vector<int>{1}));
  vpiHandle n1 = vpi_handle_by_index(By("top.n"), 1);
  ASSERT_NE(n1, nullptr);
  EXPECT_EQ(IntsOf(vpiIndex, n1), (std::vector<int>{1}));
  vpiHandle n15 = vpi_handle_by_index(n1, 5);
  ASSERT_NE(n15, nullptr);
  EXPECT_EQ(vpi_get(vpiType, n15), vpiNet);
  EXPECT_EQ(IntOf(vpi_handle(vpiIndex, n15)), 5);
  EXPECT_EQ(IntsOf(vpiIndex, n15), (std::vector<int>{5, 1}));
}

// §37.16 detail 26: a packed array net's vpiRange iteration reaches its packed
// ranges from the leftmost, an array net's its unpacked ranges, and a scalar
// net none; vpiLeftRange and vpiRightRange are the bounds of the leftmost
// packed dimension. A net in an array net is a packed array net of its own
// (#7059).
TEST_F(NetDetailsOfARun, ANetReachesTheRangesItDeclares) {
  Run("module top; wire [3:0][1:2] p; wire [7:0] a [5:4][6:8]; wire s;\n"
      "  wire [2:1] b [0:1];\n"
      "endmodule\n");
  EXPECT_EQ(BoundsOf(By("top.p")), (std::vector<int>{3, 0, 1, 2}));
  EXPECT_EQ(IntOf(vpi_handle(vpiLeftRange, By("top.p"))), 3);
  EXPECT_EQ(IntOf(vpi_handle(vpiRightRange, By("top.p"))), 0);
  EXPECT_EQ(BoundsOf(By("top.a")), (std::vector<int>{5, 4, 6, 8}));
  EXPECT_EQ(vpi_iterate(vpiRange, By("top.s")), nullptr);
  EXPECT_EQ(BoundsOf(By("top.b")), (std::vector<int>{0, 1}));
  vpiHandle b0 = vpi_handle_by_index(By("top.b"), 0);
  ASSERT_NE(b0, nullptr);
  EXPECT_EQ(BoundsOf(b0), (std::vector<int>{2, 1}));
}

// §37.16 (figure) and detail 20: vpiSimNet reaches the net an object of the
// nets class is simulated as. The run collapses no nets across the hierarchy,
// so a net, a net bit and an array net are each their own, and a net a port
// joins is no other net's. An instance is no net and has none (#7061).
TEST_F(NetDetailsOfARun, ANetIsItsOwnSimulatedNet) {
  Run("module leaf(input wire [1:0] p); endmodule\n"
      "module top; wire [1:0] w; wire a [0:1]; leaf u(w); endmodule\n");
  vpiHandle bit = vpi_handle_by_index(By("top.w"), 1);
  ASSERT_NE(bit, nullptr);
  for (vpiHandle net : {By("top.w"), bit, By("top.a"), By("top.u.p")}) {
    ASSERT_NE(net, nullptr);
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiSimNet, net)), VpiObjectOf(net));
  }
  EXPECT_EQ(vpi_handle(vpiSimNet, By("top.u")), nullptr);
}

// §37.16 (figure): a net answers vpiStrength0 and vpiStrength1 with the drive
// strengths its declaration writes, each keyword its Annex K constant, and
// with none where it writes none, an implicitly declared net among them
// (#7064).
TEST_F(NetDetailsOfARun, ANetReportsItsDeclaredDriveStrengths) {
  Run("module top;\n"
      "  wire (highz0, weak1) a = 1'b1;\n"
      "  wire (pull0, strong1) b = 1'b0;\n"
      "  wire (supply0, supply1) c = 1'b0;\n"
      "  wire d;\n"
      "  assign e = 1'b0;\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiStrength0, By("top.a")), vpiHiZ);
  EXPECT_EQ(vpi_get(vpiStrength1, By("top.a")), vpiWeakDrive);
  EXPECT_EQ(vpi_get(vpiStrength0, By("top.b")), vpiPullDrive);
  EXPECT_EQ(vpi_get(vpiStrength1, By("top.b")), vpiStrongDrive);
  EXPECT_EQ(vpi_get(vpiStrength0, By("top.c")), vpiSupplyDrive);
  EXPECT_EQ(vpi_get(vpiStrength1, By("top.c")), vpiSupplyDrive);
  EXPECT_EQ(vpi_get(vpiStrength0, By("top.d")), 0);
  ASSERT_NE(By("top.e"), nullptr);
  EXPECT_EQ(vpi_get(vpiStrength1, By("top.e")), 0);
}

// §37.16 (figure) with §6.6.4.2: a trireg net answers vpiChargeStrength with
// the charge strength it was declared with, medium where none was written,
// and a net of any other type, which holds no charge, with none (#7063).
TEST_F(NetDetailsOfARun, ATriregNetReportsItsChargeStrength) {
  Run("module top; trireg (small) s; trireg (large) l; trireg m; wire w;\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiChargeStrength, By("top.s")), vpiSmallCharge);
  EXPECT_EQ(vpi_get(vpiChargeStrength, By("top.l")), vpiLargeCharge);
  EXPECT_EQ(vpi_get(vpiChargeStrength, By("top.m")), vpiMediumCharge);
  EXPECT_EQ(vpi_get(vpiChargeStrength, By("top.w")), 0);
  EXPECT_EQ(vpi_get(vpiChargeStrength, By("top")), 0);
}

// §37.16 (figure): a net object standing for no net of the run holds no
// charge to report.
TEST(NetChargeStrength, ANetStandingForNoRunNetHoldsNoCharge) {
  VpiObject net;
  net.type = vpiNet;
  int charge = -1;
  EXPECT_TRUE(VpiGetNetStrengthProperty(vpiChargeStrength, &net, charge));
  EXPECT_EQ(charge, 0);
}

// §37.16 (figure): vpiExplicitScalared and vpiExplicitVectored say whether a
// net's declaration wrote the scalared or the vectored keyword (#7065).
TEST_F(NetDetailsOfARun, ANetReportsTheScalaredOrVectoredKeyword) {
  Run("module top; wire vectored [3:0] v; wire scalared [3:0] s;\n"
      "  wire [3:0] n;\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiExplicitVectored, By("top.v")), 1);
  EXPECT_EQ(vpi_get(vpiExplicitScalared, By("top.v")), 0);
  EXPECT_EQ(vpi_get(vpiExplicitScalared, By("top.s")), 1);
  EXPECT_EQ(vpi_get(vpiExplicitVectored, By("top.s")), 0);
  EXPECT_EQ(vpi_get(vpiExplicitScalared, By("top.n")), 0);
  EXPECT_EQ(vpi_get(vpiExplicitVectored, By("top.n")), 0);
}

// §37.16 (figure) and detail 21: a vectored net is not expanded into its bits,
// so it and its bits answer vpiExpanded FALSE, while a scalared net and one
// declared with neither keyword are expanded (#7066).
TEST_F(NetDetailsOfARun, AVectoredNetIsNotExpanded) {
  Run("module top; wire vectored [3:0] v; wire scalared [3:0] s;\n"
      "  wire [3:0] n;\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiExpanded, By("top.v")), 0);
  vpiHandle bit = vpi_handle_by_index(By("top.v"), 2);
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(vpi_get(vpiExpanded, bit), 0);
  EXPECT_EQ(vpi_get(vpiExpanded, By("top.s")), 1);
  EXPECT_EQ(vpi_get(vpiExpanded, By("top.n")), 1);
}

// §37.16 detail 33: vpiStructUnionMember is TRUE for a net whose vpiParent is
// a struct or union net, and FALSE for the struct net itself (#7069).
TEST_F(NetDetailsOfARun, AMemberOfAStructNetIsAStructUnionMember) {
  Run("module top;\n"
      "  typedef struct packed {\n"
      "    logic a; logic [1:0] b;\n"
      "    union packed { logic [1:0] x; logic [1:0] y; } u;\n"
      "  } s_t;\n"
      "  wire s_t sn;\n"
      "endmodule\n");
  vpiHandle sn = By("top.sn");
  const std::vector<vpiHandle> kMembers = ObjectsOf(vpiMember, sn);
  ASSERT_EQ(kMembers.size(), 3U);
  EXPECT_EQ(vpi_get(vpiStructUnionMember, kMembers[0]), 1);
  EXPECT_EQ(vpi_get(vpiStructUnionMember, kMembers[1]), 1);
  EXPECT_EQ(vpi_get(vpiStructUnionMember, sn), 0);
  // A member whose field is a union is a union net of its own (detail 31),
  // whose members are struct union members in turn.
  EXPECT_EQ(vpi_get(vpiType, kMembers[2]), vpiUnionNet);
  EXPECT_EQ(vpi_get(vpiPacked, kMembers[2]), 1);
  const std::vector<vpiHandle> kInner = ObjectsOf(vpiMember, kMembers[2]);
  ASSERT_EQ(kInner.size(), 2U);
  EXPECT_EQ(vpi_get(vpiStructUnionMember, kInner[0]), 1);
}

// §37.16 detail 24: an unpacked structure net's vpiSize is its number of
// members, and a packed one's, a net of an integral data type, its size in
// bits, as a packed union net's is (#7072).
TEST_F(NetDetailsOfARun, AnUnpackedStructNetsSizeIsItsMemberCount) {
  Run("module top;\n"
      "  typedef struct { logic a; logic [3:0] b; logic c; } u_t;\n"
      "  typedef struct packed { logic a; logic [1:0] b; } p_t;\n"
      "  typedef union packed { logic [4:0] x; logic [4:0] y; } pu_t;\n"
      "  wire u_t un; wire p_t pn; wire pu_t pu;\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiSize, By("top.un")), 3);
  EXPECT_EQ(vpi_get(vpiSize, By("top.pn")), 3);
  EXPECT_EQ(vpi_get(vpiPacked, By("top.pn")), 1);
  EXPECT_EQ(vpi_get(vpiType, By("top.pu")), vpiUnionNet);
  EXPECT_EQ(vpi_get(vpiSize, By("top.pu")), 5);
}

// §37.16 detail 28: a logic net with no packed dimension and a net bit are
// scalars, and a logic net with one, even of a single bit, and a net of any
// other integral data type are vectors; an array net answers as its element,
// and an unpacked structure net is neither (#7073).
TEST_F(NetDetailsOfARun, ANetIsAScalarOrAVectorByItsKind) {
  Run("module top;\n"
      "  typedef struct { logic a; logic b; } u_t;\n"
      "  wire w; wire [3:0] v; wire [0:0] o; wire integer i;\n"
      "  wire [3:0] arr [0:1]; wire u_t un;\n"
      "endmodule\n");
  // Each net's vpiScalar, then its vpiVector.
  auto shape = [](vpiHandle net) {
    return std::vector<int>{vpi_get(vpiScalar, net), vpi_get(vpiVector, net)};
  };
  EXPECT_EQ(shape(By("top.w")), (std::vector<int>{1, 0}));
  EXPECT_EQ(shape(By("top.v")), (std::vector<int>{0, 1}));
  EXPECT_EQ(shape(vpi_handle_by_index(By("top.v"), 2)),
            (std::vector<int>{1, 0}));
  EXPECT_EQ(shape(By("top.o")), (std::vector<int>{0, 1}));
  EXPECT_EQ(shape(By("top.i")), (std::vector<int>{0, 1}));
  EXPECT_EQ(shape(By("top.arr")), (std::vector<int>{0, 1}));
  EXPECT_EQ(shape(By("top.un")), (std::vector<int>{0, 0}));
}

// §37.16 detail 31: the vpiParent of a net in a multidimensional array net,
// and of a subarray of one, is the largest array net holding it, not the
// subarray it is held in (#7074, #7394).
TEST_F(NetDetailsOfARun, ANetsParentIsItsLargestArrayNet) {
  Run("module top; wire mda [1:0][1:0][2:3]; endmodule\n");
  vpiHandle mda = By("top.mda");
  vpiHandle sub = vpi_handle_by_index(mda, 1);
  ASSERT_NE(sub, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, sub)), VpiObjectOf(mda));
  vpiHandle subsub = vpi_handle_by_index(sub, 0);
  ASSERT_NE(subsub, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, subsub)), VpiObjectOf(mda));
  vpiHandle element = vpi_handle_by_index(subsub, 3);
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, element)), VpiObjectOf(mda));
}

// §37.16 detail 32: a packed array net's vpiElement iteration reaches its
// subelements one packed dimension at a time, packed array nets while
// dimensions remain and its struct, union or enum nets past the last, each
// named by its index and holding its share of the bits; detail 31 makes the
// whole packed array net the vpiParent of every one of them (#7075).
TEST_F(NetDetailsOfARun, APackedArrayNetReachesItsSubelements) {
  Run("module top;\n"
      "  typedef struct packed { integer i1; logic [1:0][2:3] bvec; } pst;\n"
      "  typedef union packed { logic [3:0] a; logic [3:0] b; } put;\n"
      "  typedef enum logic [1:0] { A, B } et;\n"
      "  wire pst [0:2][6:3] panet1; wire put [1:0] pun; wire et [1:0] en;\n"
      "endmodule\n");
  vpiHandle panet1 = By("top.panet1");
  const std::vector<vpiHandle> kRows = ObjectsOf(vpiElement, panet1);
  ASSERT_EQ(kRows.size(), 3U);
  EXPECT_EQ(vpi_get(vpiType, kRows[0]), vpiPackedArrayNet);
  EXPECT_STREQ(vpi_get_str(vpiName, kRows[0]), "panet1[0]");
  EXPECT_EQ(vpi_get(vpiSize, kRows[0]), 4 * 36);
  const std::vector<vpiHandle> kLeaves = ObjectsOf(vpiElement, kRows[0]);
  ASSERT_EQ(kLeaves.size(), 4U);
  EXPECT_EQ(vpi_get(vpiType, kLeaves[0]), vpiStructNet);
  EXPECT_STREQ(vpi_get_str(vpiName, kLeaves[0]), "panet1[0][6]");
  EXPECT_STREQ(vpi_get_str(vpiName, kLeaves[3]), "panet1[0][3]");
  EXPECT_EQ(vpi_get(vpiSize, kLeaves[0]), 36);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, kLeaves[0])),
            VpiObjectOf(panet1));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, kRows[0])), VpiObjectOf(panet1));
  const std::vector<vpiHandle> kUnions = ObjectsOf(vpiElement, By("top.pun"));
  ASSERT_EQ(kUnions.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kUnions[0]), vpiUnionNet);
  const std::vector<vpiHandle> kEnums = ObjectsOf(vpiElement, By("top.en"));
  ASSERT_EQ(kEnums.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kEnums[0]), vpiEnumNet);
}

// §37.16 detail 2: vpiPackedArrayMember is TRUE for a subelement of a packed
// array net, a packed array net or a struct net whose vpiParent is one, and
// FALSE for the packed array net itself (#7397).
TEST_F(NetDetailsOfARun, APackedArrayNetsSubelementsArePackedArrayMembers) {
  Run("module top;\n"
      "  typedef struct packed { integer i1; logic [1:0][2:3] bvec; } pst;\n"
      "  wire pst [0:2][6:3] panet1;\n"
      "endmodule\n");
  vpiHandle panet1 = By("top.panet1");
  const std::vector<vpiHandle> kRows = ObjectsOf(vpiElement, panet1);
  ASSERT_EQ(kRows.size(), 3U);
  const std::vector<vpiHandle> kLeaves = ObjectsOf(vpiElement, kRows[0]);
  ASSERT_EQ(kLeaves.size(), 4U);
  EXPECT_EQ(vpi_get(vpiPackedArrayMember, kRows[0]), 1);
  EXPECT_EQ(vpi_get(vpiPackedArrayMember, kLeaves[0]), 1);
  EXPECT_EQ(vpi_get(vpiPackedArrayMember, panet1), 0);
}

// §37.16 detail 32 with §37.26: a struct subelement of a packed array net has
// a member net per field, named under the subelement and holding the field's
// bits of that subelement's share of the net (#7393).
TEST_F(NetDetailsOfARun, APackedArrayNetsStructSubelementHasMemberNets) {
  Run("module top;\n"
      "  typedef struct packed { integer i1; logic [3:0] bvec; } pst;\n"
      "  wire pst [1:0] pn;\n"
      "  assign pn = {32'd7, 4'h9, 32'd5, 4'h3};\n"
      "endmodule\n");
  const std::vector<vpiHandle> kLeaves = ObjectsOf(vpiElement, By("top.pn"));
  ASSERT_EQ(kLeaves.size(), 2U);
  EXPECT_EQ(NamesOf(vpiMember, kLeaves[0]),
            (std::vector<std::string>{"bvec", "i1"}));
  vpiHandle bvec = Named(vpiMember, kLeaves[0], "bvec");
  ASSERT_NE(bvec, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, bvec), "top.pn[1].bvec");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, bvec)), VpiObjectOf(kLeaves[0]));
  EXPECT_EQ(IntOf(bvec), 9);
  vpiHandle i1 = Named(vpiMember, kLeaves[1], "i1");
  ASSERT_NE(i1, nullptr);
  EXPECT_EQ(IntOf(i1), 5);
}

// §37.16 detail 34: a net decompiles to the name an expression writes it by,
// with the struct nets it is a member of before it and an element's or a
// bit's index after it (#7076).
TEST_F(NetDetailsOfARun, ANetDecompilesToItsPrefixedName) {
  Run("module top;\n"
      "  typedef struct packed {\n"
      "    struct packed { logic [3:0] j1; } inner1; logic [3:0] v;\n"
      "  } s_t;\n"
      "  wire s_t str1; wire [7:0] warr1 [1:4]; wire [3:0] w;\n"
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, By("top.w")), "w");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, vpi_handle_by_index(By("top.w"), 2)),
               "w[2]");
  EXPECT_STREQ(
      vpi_get_str(vpiDecompile, vpi_handle_by_index(By("top.warr1"), 2)),
      "warr1[2]");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, By("top.str1.inner1.j1")),
               "str1.inner1.j1");
  EXPECT_STREQ(vpi_get_str(vpiName, By("top.str1.inner1.j1")), "j1");
}

// §37.16 detail 32 with §37.26 and §26.3: the struct subelements of a packed
// array net of a package's typedef have the members of that typedef, which
// the design's layouts key by the package's name (#7400).
TEST_F(NetDetailsOfARun, APackageStructsPackedArrayNetHasMemberNets) {
  Run("package pk;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } ps_t;\n"
      "endpackage\n"
      "module top;\n"
      "  wire pk::ps_t [1:0] pw;\n"
      "  assign pw = 16'h1234;\n"
      "endmodule\n");
  const std::vector<vpiHandle> kLeaves = ObjectsOf(vpiElement, By("top.pw"));
  ASSERT_EQ(kLeaves.size(), 2U);
  EXPECT_EQ(NamesOf(vpiMember, kLeaves[0]),
            (std::vector<std::string>{"a", "b"}));
  EXPECT_EQ(IntOf(Named(vpiMember, kLeaves[0], "a")), 1);
  EXPECT_EQ(IntOf(Named(vpiMember, kLeaves[1], "b")), 4);
}

// §37.16 details 1 and 32 with §37.26: a net of a packed structure written in
// place with a packed dimension of its own is a packed array net, holding no
// member itself, whose struct subelements each have a member net per field
// of the structure (#7401, #7402).
TEST_F(NetDetailsOfARun, AnInlineStructsPackedArrayNetHasMemberNets) {
  Run("module top;\n"
      "  wire struct packed { logic [3:0] a; logic [3:0] b; } [1:0] n;\n"
      "  assign n = 16'h1234;\n"
      "endmodule\n");
  vpiHandle n = By("top.n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(vpi_get(vpiType, n), vpiPackedArrayNet);
  EXPECT_TRUE(ObjectsOf(vpiMember, n).empty());
  const std::vector<vpiHandle> kLeaves = ObjectsOf(vpiElement, n);
  ASSERT_EQ(kLeaves.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kLeaves[0]), vpiStructNet);
  EXPECT_EQ(NamesOf(vpiMember, kLeaves[0]),
            (std::vector<std::string>{"a", "b"}));
  EXPECT_EQ(IntOf(Named(vpiMember, kLeaves[0], "a")), 1);
  EXPECT_EQ(IntOf(Named(vpiMember, kLeaves[1], "b")), 4);
}

// §37.16 with §6.10: vpiImplicitDecl is TRUE for a net the left side of a
// continuous assignment declares implicitly and FALSE for a declared one
// (#7067).
TEST_F(NetDetailsOfARun, AnImplicitlyDeclaredNetReportsImplicitDecl) {
  Run("module top;\n"
      "  assign y = 1'b0;\n"
      "  wire w;\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiImplicitDecl, By("top.y")), 1);
  EXPECT_EQ(vpi_get(vpiImplicitDecl, By("top.w")), 0);
}

// §37.16 detail 9: an implicitly declared net reports line 0 and the file of
// the reference that declared it, where a declared net reports its
// declaration's line (#7068).
TEST_F(NetDetailsOfARun, AnImplicitNetReportsItsFirstReferencesFileAtLineZero) {
  Run("module top;\n"
      "  assign y = 1'b0;\n"
      "  wire w;\n"
      "endmodule\n");
  vpiHandle y = By("top.y");
  EXPECT_EQ(vpi_get(vpiLineNo, y), 0);
  EXPECT_STREQ(vpi_get_str(vpiFile, y), "<test>");
  EXPECT_EQ(vpi_get(vpiLineNo, By("top.w")), 3);
}

}  // namespace
}  // namespace delta
