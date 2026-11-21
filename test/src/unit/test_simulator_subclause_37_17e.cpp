#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VariablePropertiesOfARun : public VpiDesignRun {
 protected:
  static std::vector<int> ShapeOf(vpiHandle var) {
    if (var == nullptr) return {};
    return {vpi_get(vpiScalar, var), vpi_get(vpiVector, var)};
  }

  static std::string TypeNameOf(vpiHandle obj) {
    const char* name = vpi_get_str(vpiType, obj);
    return name == nullptr ? "" : name;
  }

  static int KindIn(vpiHandle scope, const char* name) {
    return vpi_get(vpiType, Named(vpiVariables, scope, name));
  }

  static bool ValueReadIsRefused(vpiHandle var) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = 41;
    vpi_get_value(var, &value);
    s_vpi_error_info info = {};
    const PLI_INT32 kLevel = vpi_chk_error(&info);
    return kLevel == vpiError && value.value.integer == 41;
  }

  static bool ValuePutIsRefused(vpiHandle var) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = 6;
    vpiHandle event = vpi_put_value(var, &value, nullptr, vpiNoDelay);
    s_vpi_error_info info = {};
    const PLI_INT32 kLevel = vpi_chk_error(&info);
    return event == nullptr && kLevel == vpiError;
  }
};

TEST_F(VariablePropertiesOfARun, AModuleBlockOrPackageVariableIsItsTypesKind) {
  Run("package p; time t; shortint s; longint l; byte b; bit x; endpackage\n"
      "module top; time t; shortint s; longint l; byte b; bit x;\n"
      "  initial begin : blk time t; shortint s; longint l; byte b; bit x;\n"
      "  end\n"
      "endmodule\n");
  for (const char* scope_name : {"p", "top", "top.blk"}) {
    vpiHandle scope = By(scope_name);
    ASSERT_NE(scope, nullptr) << scope_name;
    EXPECT_EQ(KindIn(scope, "t"), vpiTimeVar) << scope_name;
    EXPECT_EQ(KindIn(scope, "s"), vpiShortIntVar) << scope_name;
    EXPECT_EQ(KindIn(scope, "l"), vpiLongIntVar) << scope_name;
    EXPECT_EQ(KindIn(scope, "b"), vpiByteVar) << scope_name;
    EXPECT_EQ(KindIn(scope, "x"), vpiBitVar) << scope_name;
  }
}

TEST_F(VariablePropertiesOfARun, ALogicVarOrArrayVarNamesItsTypeEitherWay) {
  Run("module top; logic [3:0] v; logic m[2]; int a[2]; endmodule\n");
  const std::string kLogic = TypeNameOf(By("top.v"));
  EXPECT_TRUE(kLogic == "vpiLogicVar" || kLogic == "vpiReg") << kLogic;
  for (const char* name : {"top.m", "top.a"}) {
    const std::string kArray = TypeNameOf(By(name));
    EXPECT_TRUE(kArray == "vpiArrayVar" || kArray == "vpiRegArray")
        << name << " " << kArray;
  }
  const std::string kBit = TypeNameOf(vpi_handle_by_index(By("top.v"), 2));
  EXPECT_TRUE(kBit == "vpiVarBit" || kBit == "vpiRegBit") << kBit;
}

TEST_F(VariablePropertiesOfARun, ABitOfATwoStateBitVarIsAVarBit) {
  Run("module top; bit [3:0] b = 4'b0110; endmodule\n");
  ASSERT_EQ(vpi_get(vpiType, By("top.b")), vpiBitVar);
  vpiHandle bit = vpi_handle_by_index(By("top.b"), 2);
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(vpi_get(vpiType, bit), vpiVarBit);
  const std::string kName = TypeNameOf(bit);
  EXPECT_TRUE(kName == "vpiVarBit" || kName == "vpiRegBit") << kName;
}

TEST_F(VariablePropertiesOfARun, ABitVarHasOneVarBitPerBit) {
  Run("module top; bit [5:2] b = 4'b0110; endmodule\n");
  const std::vector<vpiHandle> kBits = ObjectsOf(vpiBit, By("top.b"));
  ASSERT_EQ(kBits.size(), 4U);
  std::vector<int> indices;
  std::vector<int> values;
  for (vpiHandle bit : kBits) {
    EXPECT_EQ(vpi_get(vpiType, bit), vpiVarBit);
    indices.push_back(IntegerOf(vpi_handle(vpiIndex, bit)));
    values.push_back(IntegerOf(bit));
  }
  EXPECT_EQ(indices, (std::vector<int>{5, 4, 3, 2}));
  EXPECT_EQ(values, (std::vector<int>{0, 1, 1, 0}));
}

TEST_F(VariablePropertiesOfARun, OnlyALogicBitOrPackedVariableHasBits) {
  Run("module top;\n"
      "  int i; shortint si; longint li; byte by; integer ig; time t;\n"
      "  string s; real r; struct { logic a; } us; union { logic a; } uu;\n"
      "  enum logic [1:0] { A, B } e; logic ua[2];\n"
      "  bit [1:0][1:0] pa;\n"
      "  struct packed { logic [2:0] a; } ps; union packed { bit [2:0] a; } "
      "pu;\n"
      "endmodule\n");
  for (const char* name :
       {"top.i", "top.si", "top.li", "top.by", "top.ig", "top.t", "top.s",
        "top.r", "top.us", "top.uu", "top.e", "top.ua"}) {
    ASSERT_NE(By(name), nullptr) << name;
    EXPECT_EQ(vpi_iterate(vpiBit, By(name)), nullptr) << name;
  }
  EXPECT_EQ(ObjectsOf(vpiBit, By("top.pa")).size(), 4U);
  EXPECT_EQ(ObjectsOf(vpiBit, By("top.ps")).size(), 3U);
  EXPECT_EQ(ObjectsOf(vpiBit, By("top.pu")).size(), 3U);
}

TEST_F(VariablePropertiesOfARun, AnArrayElementGivesItsIndexBothWays) {
  Run("module top; int arr[5:8]; initial arr[7] = 3; endmodule\n");
  vpiHandle by_index = vpi_handle_by_index(By("top.arr"), 7);
  vpiHandle by_name = By("top.arr[7]");
  for (vpiHandle element : {by_index, by_name}) {
    ASSERT_NE(element, nullptr);
    EXPECT_EQ(IntegerOf(element), 3);
    vpiHandle index = vpi_handle(vpiIndex, element);
    ASSERT_NE(index, nullptr);
    EXPECT_EQ(IntegerOf(index), 7);
    EXPECT_EQ(IntsOf(vpiIndex, element), (std::vector<int>{7}));
  }
}

TEST_F(VariablePropertiesOfARun, APackedAggregateVariableIsAVector) {
  Run("module top;\n"
      "  struct packed { logic a; } ps; union packed { bit [1:0] a; } pu;\n"
      "  bit [1:0][3:0] pa;\n"
      "endmodule\n");
  for (const char* name : {"top.ps", "top.pu", "top.pa"}) {
    EXPECT_EQ(ShapeOf(By(name)), (std::vector<int>{0, 1})) << name;
  }
}

TEST_F(VariablePropertiesOfARun, AVarBitIsAScalar) {
  Run("module top; logic [3:0] v; endmodule\n");
  EXPECT_EQ(ShapeOf(vpi_handle_by_index(By("top.v"), 1)),
            (std::vector<int>{1, 0}));
}

TEST_F(VariablePropertiesOfARun, AnArrayVarIsShapedAsItsElement) {
  Run("module top; int a[2]; logic b[2]; endmodule\n");
  EXPECT_EQ(ShapeOf(By("top.a")), (std::vector<int>{0, 1}));
  EXPECT_EQ(ShapeOf(By("top.b")), (std::vector<int>{1, 0}));
}

TEST_F(VariablePropertiesOfARun, AnUnshapedVariableIsNeitherScalarNorVector) {
  Run("module top; class C; endclass\n"
      "  struct { int a; } us; string s; real r; C c; chandle h;\n"
      "endmodule\n");
  for (const char* name : {"top.us", "top.s", "top.r", "top.c", "top.h"}) {
    ASSERT_NE(By(name), nullptr) << name;
    EXPECT_EQ(ShapeOf(By(name)), (std::vector<int>{0, 0})) << name;
  }
}

TEST_F(VariablePropertiesOfARun, AnIntegralVariablesSizeIsItsBitWidth) {
  Run("module top;\n"
      "  int i; integer g; byte b; time t; shortint s; longint l;\n"
      "  logic [5:0] v; enum bit [2:0] { A, B } e;\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiSize, By("top.i")), 32);
  EXPECT_EQ(vpi_get(vpiSize, By("top.g")), 32);
  EXPECT_EQ(vpi_get(vpiSize, By("top.b")), 8);
  EXPECT_EQ(vpi_get(vpiSize, By("top.t")), 64);
  EXPECT_EQ(vpi_get(vpiSize, By("top.s")), 16);
  EXPECT_EQ(vpi_get(vpiSize, By("top.l")), 64);
  EXPECT_EQ(vpi_get(vpiSize, By("top.v")), 6);
  EXPECT_EQ(vpi_get(vpiSize, By("top.e")), 3);
}

TEST_F(VariablePropertiesOfARun, APackedStructOrUnionsSizeIsItsBitWidth) {
  Run("module top;\n"
      "  struct packed { logic [3:0] a; logic [6:0] b; } ps;\n"
      "  union packed { logic [4:0] a; bit [4:0] b; } pu;\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiSize, By("top.ps")), 11);
  EXPECT_EQ(vpi_get(vpiSize, By("top.pu")), 5);
}

TEST_F(VariablePropertiesOfARun, AnUnpackedUnionsSizeIsItsFieldCount) {
  Run("module top; union { int a; byte b; shortint c; } u; endmodule\n");
  EXPECT_EQ(vpi_get(vpiSize, By("top.u")), 3);
}

TEST_F(VariablePropertiesOfARun, AVariableOutsideAnArrayIsNoArrayMember) {
  Run("module top; int x; struct { int a; int b; } s; logic [7:0] v;\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiArrayMember, By("top.x")), 0);
  EXPECT_EQ(vpi_get(vpiArrayMember, By("top.s.a")), 0);
  vpiHandle bit = vpi_handle_by_index(By("top.v"), 3);
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(vpi_get(vpiArrayMember, bit), 0);
}

TEST_F(VariablePropertiesOfARun, AnElementOfAnyArrayIsAnArrayMember) {
  Run("module top; int d[]; int aa[int]; struct { int arr[3]; } s;\n"
      "  initial begin d = new[3]; aa[5] = 1; end\n"
      "endmodule\n");
  vpiHandle dynamic = vpi_handle_by_index(By("top.d"), 1);
  ASSERT_NE(dynamic, nullptr);
  EXPECT_EQ(vpi_get(vpiArrayMember, dynamic), 1);
  vpiHandle assoc = vpi_handle_by_index(By("top.aa"), 5);
  ASSERT_NE(assoc, nullptr);
  EXPECT_EQ(vpi_get(vpiArrayMember, assoc), 1);
  vpiHandle member = vpi_handle_by_index(By("top.s.arr"), 1);
  ASSERT_NE(member, nullptr);
  EXPECT_EQ(vpi_get(vpiArrayMember, member), 1);
}

TEST_F(VariablePropertiesOfARun, AUnionVariablesMemberIsAStructUnionMember) {
  Run("module top; union { int a; int b; } u; int x; endmodule\n");
  EXPECT_EQ(vpi_get(vpiStructUnionMember, By("top.u.a")), 1);
  EXPECT_EQ(vpi_get(vpiStructUnionMember, By("top.u.b")), 1);
  EXPECT_EQ(vpi_get(vpiStructUnionMember, By("top.u")), 0);
}

TEST_F(VariablePropertiesOfARun, AVirtualInterfaceVarHasNoValue) {
  Run("interface bus; endinterface\n"
      "module top; bus b(); virtual bus vif = b; endmodule\n");
  ASSERT_EQ(vpi_get(vpiType, By("top.vif")), vpiVirtualInterfaceVar);
  EXPECT_TRUE(ValueReadIsRefused(By("top.vif")));
  EXPECT_TRUE(ValuePutIsRefused(By("top.vif")));
}

TEST_F(VariablePropertiesOfARun, AnUnpackedStructOrUnionVarHasNoValue) {
  Run("module top; struct { int a; } s; union { int a; int b; } u;\n"
      "  initial begin s.a = 3; u.a = 4; end\n"
      "endmodule\n");
  for (const char* name : {"top.s", "top.u"}) {
    EXPECT_TRUE(ValueReadIsRefused(By(name))) << name;
    EXPECT_TRUE(ValuePutIsRefused(By(name))) << name;
  }
  EXPECT_EQ(IntegerOf(By("top.s.a")), 3);
  EXPECT_EQ(IntegerOf(By("top.u.a")), 4);
}

TEST_F(VariablePropertiesOfARun, APackedUnionVarHasAValue) {
  Run("module top; union packed { bit [3:0] a; logic [3:0] b; } u;\n"
      "  initial u.a = 4'd9;\n"
      "endmodule\n");
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(By("top.u"), &value);
  s_vpi_error_info info = {};
  const PLI_INT32 kLevel = vpi_chk_error(&info);
  EXPECT_EQ(kLevel, 0);
  EXPECT_EQ(value.value.integer, 9);
}

TEST_F(VariablePropertiesOfARun, AClassDefnsPropertiesReportTheirVisibility) {
  Run("module top;\n"
      "  class C; protected int b; local int a; int c; endclass\n"
      "  int v;\n"
      "endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(defn, nullptr);
  EXPECT_EQ(vpi_get(vpiVisibility, Named(vpiVariables, defn, "b")),
            vpiProtectedVis);
  EXPECT_EQ(vpi_get(vpiVisibility, Named(vpiVariables, defn, "a")),
            vpiLocalVis);
  EXPECT_EQ(vpi_get(vpiVisibility, Named(vpiVariables, defn, "c")),
            vpiPublicVis);
}

TEST_F(VariablePropertiesOfARun, AModuleVariableIsPubliclyVisible) {
  Run("module top; int v; logic [1:0] w; endmodule\n");
  EXPECT_EQ(vpi_get(vpiVisibility, By("top.v")), vpiPublicVis);
  EXPECT_EQ(vpi_get(vpiVisibility, By("top.w")), vpiPublicVis);
}

constexpr const char* kStaticMember =
    "module top;\n"
    "  class Packet; static integer Id; int n; endclass\n"
    "  Packet p = new;\n"
    "endmodule\n";

TEST_F(VariablePropertiesOfARun, AStaticMemberIsNamedThroughItsClassDefn) {
  Run(kStaticMember);
  vpiHandle defn = Named(vpiClassDefn, By("top"), "Packet");
  ASSERT_NE(defn, nullptr);
  vpiHandle through_defn = Named(vpiVariables, defn, "Id");
  ASSERT_NE(through_defn, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, through_defn), "top.Packet::Id");
}

TEST_F(
    VariablePropertiesOfARun,
    DISABLED_AStaticMemberReachedThroughAClassVarIsNamedThroughItsClassDefn) {
  Run(kStaticMember);
  vpiHandle by_name = By("top.p.Id");
  ASSERT_NE(by_name, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, by_name), "top.Packet::Id");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.p"));
  ASSERT_NE(obj, nullptr);
  vpiHandle through_obj = Named(vpiVariables, obj, "Id");
  ASSERT_NE(through_obj, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, through_obj), "top.Packet::Id");
}

}  // namespace
}  // namespace delta
