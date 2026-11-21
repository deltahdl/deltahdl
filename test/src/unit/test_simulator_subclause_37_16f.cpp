#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class NetIndicesOfARun : public VpiDesignRun {
 protected:
  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }

  static std::vector<int> IntsOf(int type, vpiHandle ref) {
    std::vector<int> values;
    for (vpiHandle obj : ObjectsOf(type, ref)) values.push_back(IntOf(obj));
    return values;
  }

  static std::vector<int> BoundsOf(vpiHandle obj) {
    std::vector<int> bounds;
    for (vpiHandle range : ObjectsOf(vpiRange, obj)) {
      bounds.push_back(IntOf(vpi_handle(vpiLeftRange, range)));
      bounds.push_back(IntOf(vpi_handle(vpiRightRange, range)));
    }
    return bounds;
  }

  static std::vector<int> LeftRightOf(vpiHandle obj) {
    return {IntOf(vpi_handle(vpiLeftRange, obj)),
            IntOf(vpi_handle(vpiRightRange, obj))};
  }

  static int KindOf(vpiHandle obj) {
    return obj == nullptr ? 0 : vpi_get(vpiType, obj);
  }

  void RunPreprocessed(const std::string& src) {
    auto fid = f_.mgr.AddFile("<test>", src);
    Preprocessor preproc(f_.mgr, f_.diag, {});
    auto text = preproc.Preprocess(fid);
    auto pp_fid = f_.mgr.AddPreprocessedFile("<preprocessed>", text,
                                             preproc.LineOrigins());
    Lexer lexer(f_.mgr.FileContent(pp_fid), pp_fid, f_.diag,
                TextOrigin::kPreprocessorOutput);
    Parser parser(lexer, f_.arena, f_.diag);
    CompilationUnit* cu = parser.Parse();
    cu->default_nettype = preproc.DefaultNetType();
    Elaborator elab(f_.arena, f_.diag, cu);
    RtlirDesign* design = elab.Elaborate("top");
    ASSERT_NE(design, nullptr);
    ASSERT_FALSE(f_.has_errors);
    LowerAndRun(design, f_);
  }

  static vpiHandle FirstRhs(vpiHandle scope) {
    const std::vector<vpiHandle> kAssigns = ObjectsOf(vpiContAssign, scope);
    return kAssigns.empty() ? nullptr : vpi_handle(vpiRhs, kAssigns[0]);
  }

  static void ExpectANettypeSelect(vpiHandle part) {
    ASSERT_NE(part, nullptr);
    EXPECT_EQ(vpi_get(vpiNetType, part), vpiNettypeNetSelect);
    EXPECT_EQ(vpi_iterate(vpiDriver, part), nullptr);
    EXPECT_EQ(vpi_iterate(vpiLocalDriver, part), nullptr);
  }

  static void ExpectMembersUnder(vpiHandle net,
                                 const std::vector<std::string>& names) {
    ASSERT_NE(net, nullptr);
    EXPECT_EQ(NamesOf(vpiMember, net), names);
    for (vpiHandle member : ObjectsOf(vpiMember, net)) {
      EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, member)), VpiObjectOf(net));
    }
  }
};

std::vector<int> PackedBounds() { return {3, 0, 1, 2}; }
std::vector<int> LeftmostBounds() { return {3, 0}; }

TEST_F(NetIndicesOfARun, DISABLED_ABitNetReachesItsPackedRangesLeftmostFirst) {
  Run("nettype bit [3:0][1:2] bv_t;\n"
      "module top; bv_t n; endmodule\n");
  EXPECT_EQ(BoundsOf(By("top.n")), PackedBounds());
  EXPECT_EQ(LeftRightOf(By("top.n")), LeftmostBounds());
}

TEST_F(NetIndicesOfARun, APackedArrayNetReachesOnlyTheDimensionsItWrites) {
  Run("typedef struct packed { logic a; logic [1:0] b; } s_t;\n"
      "typedef union packed { logic [2:0] x; logic [2:0] y; } u_t;\n"
      "typedef enum logic [1:0] { A, B } e_t;\n"
      "module top; wire s_t [3:0][1:2] sn; wire u_t [3:0][1:2] un;\n"
      "  wire e_t [3:0][1:2] en;\n"
      "endmodule\n");
  for (const char* name : {"top.sn", "top.un", "top.en"}) {
    EXPECT_EQ(BoundsOf(By(name)), PackedBounds()) << name;
    EXPECT_EQ(LeftRightOf(By(name)), LeftmostBounds()) << name;
  }
}

TEST_F(NetIndicesOfARun, ANetOutsideAnyArrayHasNoIndices) {
  Run("module top; wire s; wire [3:0] v; endmodule\n");
  EXPECT_EQ(vpi_iterate(vpiIndex, By("top.s")), nullptr);
  EXPECT_EQ(vpi_iterate(vpiIndex, By("top.v")), nullptr);
}

TEST_F(NetIndicesOfARun,
       DISABLED_APackedArrayNetsSubelementsReachTheirIndicesOutward) {
  Run("typedef struct packed { logic a; logic [1:0] b; } s_t;\n"
      "typedef union packed { logic [2:0] x; logic [2:0] y; } u_t;\n"
      "typedef enum logic [1:0] { A, B } e_t;\n"
      "module top; wire s_t [0:2][6:3] sn; wire u_t [0:2][6:3] un;\n"
      "  wire e_t [0:2][6:3] en;\n"
      "endmodule\n");
  for (const char* name : {"top.sn", "top.un", "top.en"}) {
    const std::vector<vpiHandle> kRows = ObjectsOf(vpiElement, By(name));
    ASSERT_EQ(kRows.size(), 3U) << name;
    EXPECT_EQ(IntsOf(vpiIndex, kRows[0]), (std::vector<int>{0})) << name;
    const std::vector<vpiHandle> kLeaves = ObjectsOf(vpiElement, kRows[0]);
    ASSERT_EQ(kLeaves.size(), 4U) << name;
    EXPECT_EQ(IntsOf(vpiIndex, kLeaves[0]), (std::vector<int>{6, 0})) << name;
  }
}

vpiHandle BitOfElementOfM() {
  vpiHandle element =
      vpi_handle_by_index(vpi_handle_by_name(VpiText("top.m"), nullptr), 1);
  return element == nullptr ? nullptr : vpi_handle_by_index(element, 2);
}

TEST_F(NetIndicesOfARun, ABitOfAnArrayNetElementReachesItsOwnIndex) {
  Run("module top; wire [3:0] m [0:2]; endmodule\n");
  vpiHandle bit = BitOfElementOfM();
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(IntOf(vpi_handle(vpiIndex, bit)), 2);
}

TEST_F(NetIndicesOfARun,
       DISABLED_ABitOfAnArrayNetElementIteratesItsIndicesOutward) {
  Run("module top; wire [3:0] m [0:2]; endmodule\n");
  vpiHandle bit = BitOfElementOfM();
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(IntsOf(vpiIndex, bit), (std::vector<int>{2, 1}));
}

TEST_F(NetIndicesOfARun, ANettypeNetsBitHasNoLocalDrivers) {
  Run("nettype logic [7:4] n4;\n"
      "module top; n4 n; endmodule\n");
  ExpectANettypeSelect(vpi_handle_by_index(By("top.n"), 5));
}

TEST_F(NetIndicesOfARun, DISABLED_ANettypeNetsPartSelectIsANettypeSelect) {
  Run("nettype logic [7:4] n4;\n"
      "module top; n4 n; wire [1:0] w; assign w = n[5:4]; endmodule\n");
  ExpectANettypeSelect(FirstRhs(By("top")));
}

TEST_F(NetIndicesOfARun, DISABLED_ANettypeNetsMemberIsANettypeSelect) {
  Run("typedef struct { real a; real b; } s_t; nettype s_t sn;\n"
      "module top; sn x; endmodule\n");
  ExpectANettypeSelect(Named(vpiMember, By("top.x"), "a"));
}

TEST_F(NetIndicesOfARun, DISABLED_AnArrayNetPortsLowConnReachesTheWholePort) {
  Run("module sub(input wire h [0:1]); endmodule\n"
      "module top; wire arr [0:1]; sub u(.h(arr)); endmodule\n");
  const std::vector<vpiHandle> kPorts = ObjectsOf(vpiPorts, By("top.u.h"));
  ASSERT_EQ(kPorts.size(), 1U);
  EXPECT_EQ(vpi_get(vpiType, kPorts[0]), vpiPort);
  EXPECT_STREQ(vpi_get_str(vpiName, kPorts[0]), "h");
}

TEST_F(NetIndicesOfARun, RealAndTwoStateNettypeNetsAreTheirOwnKinds) {
  Run("nettype real r_t; nettype shortreal sr_t; nettype byte by_t;\n"
      "nettype shortint si_t; nettype longint li_t;\n"
      "module top; r_t r; sr_t sr; by_t by; si_t si; li_t li; endmodule\n");
  EXPECT_EQ(KindOf(By("top.r")), vpiRealNet);
  EXPECT_EQ(KindOf(By("top.sr")), vpiShortRealNet);
  EXPECT_EQ(KindOf(By("top.by")), vpiByteNet);
  EXPECT_EQ(KindOf(By("top.si")), vpiShortIntNet);
  EXPECT_EQ(KindOf(By("top.li")), vpiLongIntNet);
}

TEST_F(NetIndicesOfARun, AggregateNettypeNetsAreTheirOwnKinds) {
  Run("typedef struct { real a; real b; } s_t;\n"
      "typedef union { real a; real b; } u_t;\n"
      "typedef enum bit [1:0] { A, B } e_t;\n"
      "nettype s_t sn_t; nettype u_t un_t; nettype e_t en_t;\n"
      "module top; sn_t s; un_t u; en_t e; endmodule\n");
  EXPECT_EQ(KindOf(By("top.s")), vpiStructNet);
  EXPECT_EQ(KindOf(By("top.u")), vpiUnionNet);
  EXPECT_EQ(KindOf(By("top.e")), vpiEnumNet);
}

TEST_F(NetIndicesOfARun, DISABLED_AnUnpackedArrayNettypeNetIsAnArrayNet) {
  Run("typedef real ua_t [0:1]; nettype ua_t uan_t;\n"
      "module top; uan_t a; endmodule\n");
  EXPECT_EQ(KindOf(By("top.a")), vpiArrayNet);
}

TEST_F(NetIndicesOfARun, UnpackedStructAndUnionNetsAreTheirOwnKinds) {
  Run("typedef struct { logic a; logic [1:0] b; } s_t;\n"
      "typedef union { logic [1:0] a; logic b; } u_t;\n"
      "module top; wire s_t s; wire u_t u; endmodule\n");
  EXPECT_EQ(KindOf(By("top.s")), vpiStructNet);
  EXPECT_EQ(KindOf(By("top.u")), vpiUnionNet);
}

TEST_F(NetIndicesOfARun, AnInterconnectIsAnInterconnectNet) {
  Run("module top; interconnect w; endmodule\n");
  EXPECT_EQ(KindOf(By("top.w")), vpiInterconnectNet);
}

TEST_F(NetIndicesOfARun, StructAndUnionNetsReachTheirMemberNets) {
  Run("typedef struct { logic a; logic [1:0] b; } s_t;\n"
      "typedef union { logic [1:0] x; logic y; } u_t;\n"
      "module top; wire union packed { logic [1:0] p; logic [1:0] q; } pu;\n"
      "  wire s_t us; wire u_t uu;\n"
      "endmodule\n");
  ExpectMembersUnder(By("top.pu"), {"p", "q"});
  ExpectMembersUnder(By("top.us"), {"a", "b"});
  ExpectMembersUnder(By("top.uu"), {"x", "y"});
}

TEST_F(NetIndicesOfARun, AnUnpackedAggregatesArrayMemberIsReached) {
  Run("typedef struct { logic [1:0] arr [0:3]; logic b; } s_t;\n"
      "typedef union { logic [1:0] arr [0:1]; logic [3:0] w; } u_t;\n"
      "module top; wire s_t sn; wire u_t un; endmodule\n");
  EXPECT_NE(Named(vpiMember, By("top.sn"), "arr"), nullptr);
  EXPECT_NE(Named(vpiMember, By("top.un"), "arr"), nullptr);
}

TEST_F(NetIndicesOfARun, MembersAndConstantElementsOfNetsAreConstantSelects) {
  Run("typedef struct packed { logic a; logic [1:0] b; } s_t;\n"
      "module top; wire s_t sn; wire [1:0] arr [0:3]; endmodule\n");
  vpiHandle member = Named(vpiMember, By("top.sn"), "b");
  ASSERT_NE(member, nullptr);
  EXPECT_EQ(vpi_get(vpiConstantSelect, member), 1);
  vpiHandle element = vpi_handle_by_index(By("top.arr"), 2);
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(vpi_get(vpiConstantSelect, element), 1);
}

TEST_F(NetIndicesOfARun, AGenvarIndexedNetBitIsAConstantSelect) {
  Run("module top; wire [7:0] a;\n"
      "  for (genvar g = 2; g < 4; g++) begin : gb\n"
      "    wire y; assign y = a[g];\n"
      "  end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kAssigns =
      ObjectsOf(vpiContAssign, By("top.gb[3]"));
  ASSERT_EQ(kAssigns.size(), 1U);
  vpiHandle rhs = vpi_handle(vpiRhs, kAssigns[0]);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(vpi_get(vpiConstantSelect, rhs), 1);
}

TEST_F(NetIndicesOfARun, ABitNetHasOneNetBitPerBit) {
  Run("nettype bit [3:0] bit_net;\n"
      "module top; bit_net b; assign b = 4'b0100; endmodule\n");
  vpiHandle b = By("top.b");
  const std::vector<vpiHandle> kBits = ObjectsOf(vpiBit, b);
  ASSERT_EQ(kBits.size(), 4U);
  EXPECT_EQ(KindOf(kBits[0]), vpiNetBit);
  EXPECT_EQ(IntsOf(vpiIndex, kBits[0]), (std::vector<int>{3}));
  EXPECT_EQ(IntsOf(vpiIndex, kBits[3]), (std::vector<int>{0}));
  vpiHandle bit2 = vpi_handle_by_index(b, 2);
  ASSERT_NE(bit2, nullptr);
  EXPECT_EQ(IntOf(bit2), 1);
}

TEST_F(NetIndicesOfARun, ANetBitAndAnArrayNetsNetCarryTheDeclaredNetType) {
  Run("module top; wand [3:0] w; tri1 t [0:1]; endmodule\n");
  vpiHandle bit = vpi_handle_by_index(By("top.w"), 2);
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(vpi_get(vpiNetType, bit), vpiWand);
  EXPECT_STREQ(vpi_get_str(vpiNetType, bit), "vpiWand");
  vpiHandle element = vpi_handle_by_index(By("top.t"), 1);
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(vpi_get(vpiNetType, element), vpiTri1);
  EXPECT_STREQ(vpi_get_str(vpiNetType, element), "vpiTri1");
}

TEST_F(NetIndicesOfARun, AnImplicitNetCarriesTheDefaultNettype) {
  Run("module top; assign y = 1'b0; endmodule\n");
  EXPECT_EQ(vpi_get(vpiNetType, By("top.y")), vpiWire);
}

TEST_F(NetIndicesOfARun, AnImplicitNetCarriesAChangedDefaultNettype) {
  RunPreprocessed(
      "`default_nettype tri0\n"
      "module top; assign z = 1'b0; endmodule\n");
  EXPECT_EQ(vpi_get(vpiNetType, By("top.z")), vpiTri0);
  EXPECT_STREQ(vpi_get_str(vpiNetType, By("top.z")), "vpiTri0");
}

}  // namespace
}  // namespace delta
