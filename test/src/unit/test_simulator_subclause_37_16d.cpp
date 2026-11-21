#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class NetPropertiesOfARun : public VpiDesignRun {
 protected:
  static void RegisterTask(const char* name, PLI_INT32 (*calltf)(PLI_BYTE8*)) {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText(name);
    data.calltf = calltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  static int KindOf(vpiHandle obj) {
    return obj == nullptr ? 0 : vpi_get(vpiType, obj);
  }

  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }

  static std::vector<int> BoundsOf(vpiHandle obj) {
    std::vector<int> bounds;
    for (vpiHandle range : ObjectsOf(vpiRange, obj)) {
      bounds.push_back(IntOf(vpi_handle(vpiLeftRange, range)));
      bounds.push_back(IntOf(vpi_handle(vpiRightRange, range)));
    }
    return bounds;
  }

  struct ValueRead {
    PLI_INT32 level;
    int value;
  };

  static ValueRead ReadValue(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = 0x5A5A;
    vpi_get_value(obj, &value);
    s_vpi_error_info info = {};
    PLI_INT32 level = vpi_chk_error(&info);
    return {level, value.value.integer};
  }

  static int CountOf(int relation, vpiHandle ref, int kind) {
    std::vector<vpiHandle> objects = ObjectsOf(relation, ref);
    return static_cast<int>(std::ranges::count_if(
        objects,
        [kind](vpiHandle obj) { return vpi_get(vpiType, obj) == kind; }));
  }

  static std::vector<VpiObject*> SortedOf(int relation, vpiHandle ref) {
    std::vector<VpiObject*> objects;
    for (vpiHandle obj : ObjectsOf(relation, ref)) {
      objects.push_back(VpiObjectOf(obj));
    }
    std::ranges::sort(objects);
    return objects;
  }

  static std::vector<std::vector<int>>& Counts() {
    static std::vector<std::vector<int>> counts;
    return counts;
  }

  static PLI_INT32 CountForcesAndAssigns(PLI_BYTE8*) {
    vpiHandle n = By("top.n");
    vpiHandle q = By("top.q");
    Counts().push_back(
        {CountOf(vpiLoad, n, vpiForce), CountOf(vpiLoad, n, vpiAssignStmt),
         CountOf(vpiLoad, vpi_handle_by_index(n, 1), vpiForce),
         CountOf(vpiDriver, q, vpiForce),
         CountOf(vpiDriver, vpi_handle_by_index(q, 0), vpiForce)});
    return 0;
  }

  struct SelectSets {
    std::vector<VpiObject*> select_drivers;
    std::vector<VpiObject*> bit_drivers;
    std::vector<VpiObject*> select_loads;
    std::vector<VpiObject*> bit_loads;
  };

  static std::vector<SelectSets>& Sets() {
    static std::vector<SelectSets> sets;
    return sets;
  }

  static vpiHandle RhsOfAssignTo(const char* lhs) {
    for (vpiHandle assign : ObjectsOf(vpiContAssign, By("top"))) {
      const char* name = vpi_get_str(vpiName, vpi_handle(vpiLhs, assign));
      if (name != nullptr && std::string(name) == lhs) {
        return vpi_handle(vpiRhs, assign);
      }
    }
    return nullptr;
  }

  static PLI_INT32 RecordSelectSets(PLI_BYTE8*) {
    vpiHandle select = RhsOfAssignTo("y");
    vpiHandle bit = vpi_handle_by_index(By("top.n"), IntOf(By("top.i")));
    Sets().push_back({SortedOf(vpiDriver, select), SortedOf(vpiDriver, bit),
                      SortedOf(vpiLoad, select), SortedOf(vpiLoad, bit)});
    return 0;
  }

  void ExpectRefused(const std::vector<const char*>& names) {
    Run("typedef struct { logic a; logic [3:0] b; } s_t;\n"
        "typedef union { logic [3:0] x; logic [3:0] y; } u_t;\n"
        "module top; wire [3:0] an [0:2]; wire s_t sn; wire u_t un;\n"
        "  interconnect [3:0] ic [0:1];\n"
        "endmodule\n");
    for (const char* name : names) {
      vpiHandle net = By(name);
      ASSERT_NE(net, nullptr) << name;
      const ValueRead kRead = ReadValue(net);
      EXPECT_EQ(kRead.level, vpiError) << name;
      EXPECT_EQ(kRead.value, 0x5A5A) << name;
    }
  }
};

TEST_F(NetPropertiesOfARun, VpiPackedOfAUnionVarFollowsItsDeclaration) {
  Run("module top; union packed { logic [3:0] x; logic [3:0] y; } p;\n"
      "  union { int x; real y; } u;\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiPacked, By("top.p")), 1);
  EXPECT_EQ(vpi_get(vpiPacked, By("top.u")), 0);
}

TEST_F(NetPropertiesOfARun, VpiPackedOfAnUnpackedStructOrUnionNetIsFalse) {
  Run("typedef struct { logic a; logic [3:0] b; } u_t;\n"
      "typedef union { logic [3:0] x; logic [3:0] y; } uu_t;\n"
      "module top; wire u_t sn; wire uu_t un; endmodule\n");
  EXPECT_EQ(KindOf(By("top.sn")), vpiStructNet);
  EXPECT_EQ(vpi_get(vpiPacked, By("top.sn")), 0);
  EXPECT_EQ(KindOf(By("top.un")), vpiUnionNet);
  EXPECT_EQ(vpi_get(vpiPacked, By("top.un")), 0);
}

TEST_F(NetPropertiesOfARun, UnpackedStructAndUnionNetsRefuseVpiGetValue) {
  ExpectRefused({"top.sn", "top.un"});
}

TEST_F(NetPropertiesOfARun,
       DISABLED_ArrayNetsAndInterconnectArraysRefuseVpiGetValue) {
  ExpectRefused({"top.an", "top.ic"});
}

TEST_F(NetPropertiesOfARun, APackedStructNetGivesItsValue) {
  Run("typedef struct packed { logic a; logic [3:0] b; } p_t;\n"
      "module top; wire p_t n = 5'b10110; endmodule\n");
  const ValueRead kRead = ReadValue(By("top.n"));
  EXPECT_EQ(kRead.level, 0);
  EXPECT_EQ(kRead.value, 22);
}

TEST_F(NetPropertiesOfARun,
       DISABLED_OnlyActiveForcesAndAssignsAreLoadsAndDrivers) {
  Counts().clear();
  RegisterTask("$count", &CountForcesAndAssigns);
  Run("module top; wire [1:0] n; logic [1:0] m; logic o, ob, v;\n"
      "  wire [1:0] q;\n"
      "  initial begin $count;\n"
      "    repeat (2) begin\n"
      "      #1 force o = n; assign v = n; force ob = n[1]; force q = m;\n"
      "      #1 $count;\n"
      "      #1 release o; deassign v; release ob; release q;\n"
      "      #1 $count;\n"
      "    end\n"
      "  end\n"
      "  initial if (0) force q = m;\n"
      "endmodule\n");
  const std::vector<int> kNone{0, 0, 0, 0, 0};
  const std::vector<int> kActive{1, 1, 1, 1, 1};
  EXPECT_EQ(Counts(), (std::vector<std::vector<int>>{kNone, kActive, kNone,
                                                     kActive, kNone}));
}

TEST_F(NetPropertiesOfARun,
       DISABLED_AVariableBitSelectFollowsTheBitAtTheIteration) {
  Sets().clear();
  RegisterTask("$sets", &RecordSelectSets);
  Run("module top; wire [3:0] n; logic [3:0] a; wire l0, l1, l2, l3, y;\n"
      "  int i = 1;\n"
      "  assign n[0] = a[0]; assign n[1] = a[1];\n"
      "  assign n[2] = a[2]; assign n[3] = a[3];\n"
      "  assign l0 = n[0]; assign l1 = n[1];\n"
      "  assign l2 = n[2]; assign l3 = n[3];\n"
      "  assign y = n[i];\n"
      "  initial begin #1 $sets; #1 i = 2; #1 $sets; end\n"
      "endmodule\n");
  ASSERT_EQ(Sets().size(), 2U);
  for (const SelectSets& sets : Sets()) {
    EXPECT_FALSE(sets.bit_drivers.empty());
    EXPECT_EQ(sets.select_drivers, sets.bit_drivers);
    EXPECT_EQ(sets.select_loads, sets.bit_loads);
  }
  EXPECT_NE(Sets()[0].select_drivers, Sets()[1].select_drivers);
}

TEST_F(NetPropertiesOfARun, AnInterconnectArrayHasNoTypespec) {
  Run("module top; interconnect q [0:1]; interconnect r [0:1][0:2];\n"
      "endmodule\n");
  vpiHandle r0 = vpi_handle_by_index(By("top.r"), 0);
  for (vpiHandle array : {By("top.q"), By("top.r"), r0}) {
    ASSERT_NE(array, nullptr);
    EXPECT_EQ(KindOf(array), vpiInterconnectArray);
    EXPECT_EQ(vpi_handle(vpiTypespec, array), nullptr);
  }
}

TEST_F(NetPropertiesOfARun, VpiArrayMemberIsFalseOutsideAndOnTheArrayItself) {
  Run("module top; wire [3:0] w; wire [3:0] n [0:1]; endmodule\n");
  EXPECT_EQ(vpi_get(vpiArrayMember, By("top.w")), 0);
  EXPECT_EQ(vpi_get(vpiArrayMember, By("top.n")), 0);
  EXPECT_EQ(vpi_get(vpiArrayMember, vpi_handle_by_index(By("top.n"), 0)), 1);
}

TEST_F(NetPropertiesOfARun, UnionAndEnumElementsArePackedArrayMembers) {
  Run("typedef union packed { logic [3:0] a; logic [3:0] b; } put;\n"
      "typedef enum logic [1:0] {A, B} et;\n"
      "module top; wire put [1:0] pun; wire et [1:0] en; endmodule\n");
  for (const char* name : {"top.pun", "top.en"}) {
    std::vector<vpiHandle> elements = ObjectsOf(vpiElement, By(name));
    EXPECT_EQ(elements.size(), 2U) << name;
    for (vpiHandle element : elements) {
      EXPECT_EQ(vpi_get(vpiPackedArrayMember, element), 1) << name;
    }
  }
}

TEST_F(NetPropertiesOfARun, ALoneStructNetIsNoPackedArrayMember) {
  Run("typedef struct packed { logic a; logic [3:0] b; } pst;\n"
      "module top; wire pst s; endmodule\n");
  EXPECT_EQ(vpi_get(vpiPackedArrayMember, By("top.s")), 0);
}

TEST_F(NetPropertiesOfARun, DISABLED_VpiSignedOfANetIsItsDeclaredSign) {
  Run("nettype int ni_t;\n"
      "module top; wire signed [3:0] s; wire [3:0] u; ni_t i;\n"
      "  wire integer g;\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiSigned, By("top.s")), 1);
  EXPECT_EQ(vpi_get(vpiSigned, By("top.i")), 1);
  EXPECT_EQ(vpi_get(vpiSigned, By("top.g")), 1);
}

TEST_F(NetPropertiesOfARun, AnUnsignedNetIsUnsigned) {
  Run("module top; wire [3:0] u; endmodule\n");
  EXPECT_EQ(vpi_get(vpiSigned, By("top.u")), 0);
}

TEST_F(NetPropertiesOfARun, ANetBitIsUnsigned) {
  Run("module top; wire signed [3:0] s; wire [3:0] u; endmodule\n");
  for (const char* name : {"top.s", "top.u"}) {
    vpiHandle bit = vpi_handle_by_index(By(name), 1);
    ASSERT_NE(bit, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiSigned, bit), 0) << name;
  }
}

TEST_F(NetPropertiesOfARun, DISABLED_VpiNetDeclAssignIsTrueForADeclAssignment) {
  Run("module top; wire d = 1'b1; wire c; assign c = 1'b1; endmodule\n");
  EXPECT_EQ(vpi_get(vpiNetDeclAssign, By("top.d")), 1);
}

TEST_F(NetPropertiesOfARun, VpiNetDeclAssignIsFalseForASeparateAssignment) {
  Run("module top; wire c; assign c = 1'b1; endmodule\n");
  EXPECT_EQ(vpi_get(vpiNetDeclAssign, By("top.c")), 0);
}

std::string TerminalsDesign() {
  return "module top(input a, b, clk, output o, x); wire [1:0] w;\n"
         "  and g(o, a, b); and h(x, w[0], w[1]);\n"
         "  specify (a => o) = 1; $setup(a, posedge clk, 1); endspecify\n"
         "endmodule\n";
}

TEST_F(NetPropertiesOfARun, AScalarNetIteratesItsPrimitiveTerminals) {
  Run(TerminalsDesign());
  vpiHandle a = Named(vpiNet, By("top"), "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(ObjectsOf(vpiPrimTerm, a).size(), 1U);
}

TEST_F(NetPropertiesOfARun, DISABLED_ANetAndABitIterateTheirOtherTerminals) {
  Run(TerminalsDesign());
  vpiHandle a = Named(vpiNet, By("top"), "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(ObjectsOf(vpiPathTerm, a).size(), 1U);
  EXPECT_EQ(ObjectsOf(vpiTchkTerm, a).size(), 1U);
  EXPECT_EQ(ObjectsOf(vpiPrimTerm, vpi_handle_by_index(By("top.w"), 0)).size(),
            1U);
}

TEST_F(NetPropertiesOfARun, AVectorNetsBitHasTheNetAsParent) {
  Run("module top; wire [3:0] w; endmodule\n");
  VpiObject* w = VpiObjectOf(By("top.w"));
  std::vector<vpiHandle> bits = ObjectsOf(vpiBit, By("top.w"));
  ASSERT_EQ(bits.size(), 4U);
  for (vpiHandle bit : bits) {
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, bit)), w);
  }
  EXPECT_EQ(
      VpiObjectOf(vpi_handle(vpiParent, vpi_handle_by_index(By("top.w"), 2))),
      w);
}

TEST_F(NetPropertiesOfARun, PackedUnionAndEnumNetsWithDimsArePackedArrays) {
  Run("typedef union packed { logic [3:0] a; logic [3:0] b; } pu_t;\n"
      "typedef enum logic [1:0] {A, B} e_t;\n"
      "module top; wire pu_t [1:0] u; wire e_t [3:0] e; endmodule\n");
  EXPECT_EQ(KindOf(By("top.u")), vpiPackedArrayNet);
  EXPECT_EQ(KindOf(By("top.e")), vpiPackedArrayNet);
}

TEST_F(NetPropertiesOfARun, RangesOfAStructNetAreOnlyItsExplicitOnes) {
  Run("typedef struct packed { logic [1:0] vec1; integer i1; } ps_t;\n"
      "typedef enum logic [1:0] {A, B} e_t;\n"
      "module top; wire ps_t psnet; wire ps_t [3:0][2:1] panet;\n"
      "  wire ps_t [3:0][2:1] anet [5:4][6:8]; wire e_t [3:0] en;\n"
      "endmodule\n");
  EXPECT_EQ(vpi_iterate(vpiRange, By("top.psnet")), nullptr);
  EXPECT_EQ(BoundsOf(By("top.panet")), (std::vector<int>{3, 0, 2, 1}));
  EXPECT_EQ(BoundsOf(By("top.anet")), (std::vector<int>{5, 4, 6, 8}));
  EXPECT_EQ(BoundsOf(By("top.en")), (std::vector<int>{3, 0}));
}

}  // namespace
}  // namespace delta
