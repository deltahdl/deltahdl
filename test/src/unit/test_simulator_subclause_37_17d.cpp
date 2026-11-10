#include <gtest/gtest.h>

#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/class_object.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VariablesOfARun : public VpiDesignRun {
 protected:
  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }
};

TEST_F(VariablesOfARun, ATypedefPackedVectorVariableHasBits) {
  Run("typedef logic [2:0] t3;\n"
      "module top; t3 a; logic [2:0] b; endmodule\n");
  EXPECT_EQ(ObjectsOf(vpiBit, By("top.a")).size(), 3U);
  EXPECT_EQ(ObjectsOf(vpiBit, By("top.b")).size(), 3U);
}

TEST_F(VariablesOfARun, ATypedefNamedVariableIsTheKindItsTypedefNames) {
  Run("interface bus; endinterface\n"
      "package p; typedef struct { int a; int b; } ps_t; endpackage\n"
      "module top; bus b();\n"
      "  typedef int myint; typedef virtual bus vbus_t;\n"
      "  myint x; vbus_t vif; p::ps_t s;\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, By("top.x")), vpiIntVar);
  EXPECT_EQ(vpi_get(vpiType, By("top.vif")), vpiVirtualInterfaceVar);
  EXPECT_EQ(vpi_get(vpiType, By("top.s")), vpiStructVar);
}

TEST_F(VariablesOfARun, AModulesChandleVariableIsAChandleVar) {
  Run("module top; chandle h; endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, By("top.h")), vpiChandleVar);
}

TEST_F(VariablesOfARun, AnArrayElementIsAVariableOfItsElementType) {
  Run("module top; int a[4]; byte c[2]; logic [3:0] m[2]; endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_index(By("top.a"), 0)), vpiIntVar);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_index(By("top.c"), 1)), vpiByteVar);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_index(By("top.m"), 0)), vpiReg);
  EXPECT_EQ(vpi_get(vpiIsMemory, By("top.a")), 0);
  EXPECT_EQ(vpi_get(vpiIsMemory, By("top.m")), 1);
}

TEST_F(VariablesOfARun, AVariableReachesThePortsItConnects) {
  Run("module m(output logic [3:0] v); endmodule\n"
      "module top; logic [3:0] w; m u(w); endmodule\n");
  vpiHandle port = Named(vpiPort, By("top.u"), "v");
  ASSERT_NE(port, nullptr);
  std::vector<vpiHandle> ports = ObjectsOf(vpiPorts, By("top.u.v"));
  ASSERT_EQ(ports.size(), 1U);
  EXPECT_EQ(VpiObjectOf(ports[0]), VpiObjectOf(port));
  std::vector<vpiHandle> insts = ObjectsOf(vpiPortInst, By("top.w"));
  ASSERT_EQ(insts.size(), 1U);
  EXPECT_EQ(VpiObjectOf(insts[0]), VpiObjectOf(port));
}

TEST_F(VariablesOfARun, AnArrayVarReachesItsVarSelects) {
  Run("module top; int a[4]; int i; initial a[i] = 1; endmodule\n");
  std::vector<vpiHandle> selects = ObjectsOf(vpiVarSelect, By("top.a"));
  ASSERT_EQ(selects.size(), 1U);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, selects[0])),
            VpiObjectOf(By("top.a")));
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_index(By("top.a"), 0)), vpiIntVar);
}

TEST_F(VariablesOfARun, ABuiltInTypedVariableHasAnUnnamedTypespec) {
  Run("module top; int x; byte b; endmodule\n");
  vpiHandle int_spec = vpi_handle(vpiTypespec, By("top.x"));
  ASSERT_NE(int_spec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, int_spec), vpiIntTypespec);
  EXPECT_EQ(vpi_get_str(vpiName, int_spec), nullptr);
  vpiHandle byte_spec = vpi_handle(vpiTypespec, By("top.b"));
  ASSERT_NE(byte_spec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, byte_spec), vpiByteTypespec);
}

TEST_F(VariablesOfARun, AVariableReportsItsRandomization) {
  Run("module top;\n"
      "  class C; rand int r; randc bit [1:0] k; rand int off; int n;\n"
      "    static rand int s; rand int back;\n"
      "  endclass\n"
      "  C c = new; int x;\n"
      "  initial begin\n"
      "    c.off.rand_mode(0); c.back.rand_mode(0); c.back.rand_mode(1);\n"
      "  end\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.c"));
  ASSERT_NE(obj, nullptr);
  EXPECT_EQ(vpi_get(vpiRandType, Named(vpiVariables, obj, "r")), vpiRand);
  EXPECT_EQ(vpi_get(vpiRandType, Named(vpiVariables, obj, "k")), vpiRandC);
  EXPECT_EQ(vpi_get(vpiRandType, Named(vpiVariables, obj, "n")), vpiNotRand);
  EXPECT_EQ(vpi_get(vpiRandType, By("top.x")), vpiNotRand);
  EXPECT_EQ(vpi_get(vpiIsRandomized, Named(vpiVariables, obj, "r")), 1);
  EXPECT_EQ(vpi_get(vpiIsRandomized, Named(vpiVariables, obj, "off")), 0);
  EXPECT_EQ(vpi_get(vpiIsRandomized, Named(vpiVariables, obj, "n")), 0);
  EXPECT_EQ(vpi_get(vpiIsRandomized, Named(vpiVariables, obj, "k")), 1);
  EXPECT_EQ(vpi_get(vpiIsRandomized, Named(vpiVariables, obj, "s")), 1);
  EXPECT_EQ(vpi_get(vpiIsRandomized, Named(vpiVariables, obj, "back")), 1);
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(defn, nullptr);
  EXPECT_EQ(vpi_get(vpiIsRandomized, Named(vpiVariables, defn, "r")), 1);
  EXPECT_EQ(vpi_get_str(vpiFullName, Named(vpiVariables, defn, "r")), nullptr);
  EXPECT_EQ(vpi_get(vpiRandType, By("top")), vpiUndefined);
}

TEST_F(VariablesOfARun, OnlyAnArrayVarHasAnArrayType) {
  Run("module top; int q[$]; wire w[2]; logic l; endmodule\n");
  EXPECT_EQ(vpi_get(vpiArrayType, By("top.q")), vpiQueueArray);
  ASSERT_EQ(vpi_get(vpiType, By("top.w")), vpiArrayNet);
  EXPECT_EQ(vpi_get(vpiArrayType, By("top.w")), vpiUndefined);
  EXPECT_EQ(vpi_get(vpiArrayType, By("top.l")), vpiUndefined);
}

TEST(VariablesStandingAlone, ReportTheirRandomizationNameAndDecompile) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  ClassObject holder;
  holder.rand_active["s"] = false;
  VpiObject s;
  s.type = vpiIntVar;
  s.name = "s";
  s.rand_type = vpiRand;
  s.property_of = &holder;
  EXPECT_EQ(vpi_get(vpiIsRandomized, VpiHandleOf(&s)), 0);

  VpiObject v;
  v.type = vpiIntVar;
  v.name = "v";
  EXPECT_STREQ(vpi_get_str(vpiFullName, VpiHandleOf(&v)), "v");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, VpiHandleOf(&v)), "v");
  SetGlobalVpiContext(nullptr);
}

TEST_F(VariablesOfARun, AStructMemberIsAStructUnionMember) {
  Run("module top; struct { int i1; } s; int x; endmodule\n");
  EXPECT_EQ(vpi_get(vpiStructUnionMember, By("top.s.i1")), 1);
  EXPECT_EQ(vpi_get(vpiStructUnionMember, By("top.x")), 0);
}

TEST_F(VariablesOfARun, AConstVariableIsAConstantVariable) {
  Run("module top;\n"
      "  class C; const int c = 3; int d; endclass\n"
      "  const int k = 5; int x; C o = new;\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiConstantVariable, By("top.k")), 1);
  EXPECT_EQ(vpi_get(vpiConstantVariable, By("top.x")), 0);
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.o"));
  ASSERT_NE(obj, nullptr);
  EXPECT_EQ(vpi_get(vpiConstantVariable, Named(vpiVariables, obj, "c")), 1);
  EXPECT_EQ(vpi_get(vpiConstantVariable, Named(vpiVariables, obj, "d")), 0);
}

TEST_F(VariablesOfARun, AClassObjectsPropertyReportsItsVisibility) {
  Run("module top;\n"
      "  class C; local int a; protected int b; int c; endclass\n"
      "  C o = new;\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.o"));
  ASSERT_NE(obj, nullptr);
  EXPECT_EQ(vpi_get(vpiVisibility, Named(vpiVariables, obj, "a")), vpiLocalVis);
  EXPECT_EQ(vpi_get(vpiVisibility, Named(vpiVariables, obj, "b")),
            vpiProtectedVis);
  EXPECT_EQ(vpi_get(vpiVisibility, Named(vpiVariables, obj, "c")),
            vpiPublicVis);
}

TEST_F(VariablesOfARun, AVarSelectReachesItsIndicesAndSize) {
  Run("module top; logic [7:0] r[4]; int m[4][4]; int i, j;\n"
      "  initial begin r[i] = 0; m[i][j] = 1; end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
  ASSERT_EQ(kProcs.size(), 1U);
  const std::vector<vpiHandle> kAssigns =
      ObjectsOf(vpiStmt, vpi_handle(vpiStmt, kProcs[0]));
  ASSERT_EQ(kAssigns.size(), 2U);
  vpiHandle r_i = vpi_handle(vpiLhs, kAssigns[0]);
  ASSERT_NE(r_i, nullptr);
  EXPECT_EQ(vpi_get(vpiType, r_i), vpiVarSelect);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiIndex, r_i)), VpiObjectOf(By("top.i")));
  EXPECT_EQ(vpi_get(vpiSize, r_i), 8);
  vpiHandle m_ij = vpi_handle(vpiLhs, kAssigns[1]);
  ASSERT_NE(m_ij, nullptr);
  EXPECT_EQ(vpi_get(vpiType, m_ij), vpiVarSelect);
  const std::vector<vpiHandle> kIndices = ObjectsOf(vpiIndex, m_ij);
  ASSERT_EQ(kIndices.size(), 2U);
  EXPECT_EQ(VpiObjectOf(kIndices[0]), VpiObjectOf(By("top.j")));
  EXPECT_EQ(VpiObjectOf(kIndices[1]), VpiObjectOf(By("top.i")));
  EXPECT_EQ(vpi_get(vpiSize, m_ij), 32);
}

TEST_F(VariablesOfARun, AVariableReachesItsInitializationExpression) {
  Run("module top; int k = 2; int x = k + 5; int y; endmodule\n");
  vpiHandle init = vpi_handle(vpiExpr, By("top.x"));
  ASSERT_NE(init, nullptr);
  EXPECT_EQ(vpi_get(vpiType, init), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, init), vpiAddOp);
  EXPECT_EQ(vpi_handle(vpiExpr, By("top.y")), nullptr);
}

TEST_F(VariablesOfARun, APackedStructVariableIsPackedAndHasAValue) {
  Run("typedef struct packed { logic a, b; } s_t;\n"
      "module top; s_t s = 2'b10; struct { int a; } u; endmodule\n");
  EXPECT_EQ(vpi_get(vpiPacked, By("top.s")), 1);
  EXPECT_EQ(vpi_get(vpiPacked, By("top.u")), 0);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(By("top.s"), &value);
  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
  EXPECT_EQ(value.value.integer, 2);
}

TEST_F(VariablesOfARun, AnArrayOrClassVariableHasNoValue) {
  Run("module top; class C; endclass int a[4]; C c; endmodule\n");
  for (const char* name : {"top.a", "top.c"}) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = 77;
    vpi_get_value(By(name), &value);
    s_vpi_error_info info = {};
    EXPECT_EQ(vpi_chk_error(&info), vpiError) << name;
    EXPECT_EQ(value.value.integer, 77) << name;
  }
}

TEST_F(VariablesOfARun, AValuePutToAnArrayOrClassVariableIsRefused) {
  Run("module top; class D; endclass int m[2]; D d; endmodule\n");
  for (const char* name : {"top.m", "top.d"}) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = 5;
    EXPECT_EQ(vpi_put_value(By(name), &value, nullptr, vpiNoDelay), nullptr)
        << name;
    s_vpi_error_info info = {};
    ASSERT_EQ(vpi_chk_error(&info), vpiError) << name;
    EXPECT_STREQ(info.message,
                 "vpi_put_value(): an array, class or virtual interface "
                 "variable has no value")
        << name;
  }
}

TEST_F(VariablesOfARun, AMemberOrElementIsAScalarOrAVectorByItsType) {
  Run("module top;\n"
      "  struct { int i1; logic l; logic [3:0] v; } s;\n"
      "  int a[2]; logic b[2];\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiVector, By("top.s.i1")), 1);
  EXPECT_EQ(vpi_get(vpiScalar, By("top.s.l")), 1);
  EXPECT_EQ(vpi_get(vpiVector, By("top.s.l")), 0);
  EXPECT_EQ(vpi_get(vpiVector, By("top.s.v")), 1);
  EXPECT_EQ(vpi_get(vpiVector, vpi_handle_by_index(By("top.a"), 0)), 1);
  EXPECT_EQ(vpi_get(vpiScalar, vpi_handle_by_index(By("top.b"), 1)), 1);
}

TEST_F(VariablesOfARun, ANonStaticClassDataMemberHasNoFullName) {
  Run("module top;\n"
      "  class Packet; int n; endclass\n"
      "  Packet p = new;\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.p"));
  ASSERT_NE(obj, nullptr);
  vpiHandle n = Named(vpiVariables, obj, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(vpi_get_str(vpiFullName, n), nullptr);
  vpiHandle found = vpi_handle_by_name(VpiText("top.p.n"), nullptr);
  ASSERT_NE(found, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, found), "n");
  EXPECT_EQ(vpi_get_str(vpiFullName, found), nullptr);
}

TEST_F(VariablesOfARun, ANestedStructureMemberHasMembers) {
  Run("typedef struct { int j1; int j2; } in_t;\n"
      "module top; struct { in_t inner1; int k; } str1;\n"
      "  initial begin str1.inner1.j1 = 7; str1.inner1.j2 = 9; end\n"
      "endmodule\n");
  vpiHandle j2 = By("top.str1.inner1.j2");
  ASSERT_NE(j2, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, j2)),
            VpiObjectOf(By("top.str1.inner1")));
  EXPECT_EQ(IntOf(By("top.str1.inner1.j1")), 7);
  EXPECT_EQ(IntOf(j2), 9);
}

TEST_F(VariablesOfARun, AStructureMemberHasBits) {
  Run("module top;\n"
      "  struct { logic [7:0] vec; bit [1:0][3:0] pv;\n"
      "           struct packed { logic a; logic [2:0] b; } ps; } str1;\n"
      "  initial str1.vec = 8'h20;\n"
      "endmodule\n");
  EXPECT_EQ(ObjectsOf(vpiBit, By("top.str1.vec")).size(), 8U);
  EXPECT_EQ(ObjectsOf(vpiBit, By("top.str1.pv")).size(), 8U);
  EXPECT_EQ(ObjectsOf(vpiBit, By("top.str1.ps")).size(), 4U);
  EXPECT_EQ(IntOf(vpi_handle_by_index(By("top.str1.vec"), 5)), 1);
  EXPECT_EQ(IntOf(vpi_handle_by_index(By("top.str1.vec"), 4)), 0);
}

TEST_F(VariablesOfARun, AMemberOfANamedElementTypeHasBits) {
  Run("typedef bit b_t;\n"
      "typedef logic [3:0] n_t;\n"
      "module top;\n"
      "  struct { b_t [7:0] bv; n_t [1:0] nv; } str1;\n"
      "  initial str1.bv = 8'h20;\n"
      "endmodule\n");
  EXPECT_EQ(ObjectsOf(vpiBit, By("top.str1.bv")).size(), 8U);
  EXPECT_EQ(ObjectsOf(vpiBit, By("top.str1.nv")).size(), 8U);
  EXPECT_EQ(IntOf(vpi_handle_by_index(By("top.str1.bv"), 5)), 1);
  EXPECT_EQ(IntOf(vpi_handle_by_index(By("top.str1.bv"), 4)), 0);
}

TEST_F(VariablesOfARun, AnElementOfAnArrayOfStructuresHasMembers) {
  Run("typedef struct { logic [7:0] bvec; int n; } s_t;\n"
      "module top; s_t spa[2][3];\n"
      "  initial spa[1][2].bvec = 8'h11;\n"
      "endmodule\n");
  PLI_INT32 indices[] = {1, 2};
  vpiHandle element = vpi_handle_by_multi_index(By("top.spa"), 2, indices);
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(vpi_get(vpiType, element), vpiStructVar);
  vpiHandle bvec = Named(vpiMember, element, "bvec");
  ASSERT_NE(bvec, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, bvec)), VpiObjectOf(element));
  EXPECT_EQ(IntOf(bvec), 0x11);
}

TEST_F(VariablesOfARun, AVariableDecompilesToItsPrefixedName) {
  Run("module top;\n"
      "  struct { struct { int j1; } inner1; logic [3:0] v; } str1; int x;\n"
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, By("top.x")), "x");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, By("top.str1.inner1.j1")),
               "str1.inner1.j1");
  EXPECT_STREQ(
      vpi_get_str(vpiDecompile, vpi_handle_by_index(By("top.str1.v"), 2)),
      "str1.v[2]");
}

TEST_F(VariablesOfARun, AnUnpackedArrayMemberIsAnArrayVar) {
  Run("module top; struct { logic [3:0] a[2]; int n; } s;\n"
      "  initial begin s.a[0] = 4'h3; s.a[1] = 4'h9; end\n"
      "endmodule\n");
  vpiHandle a = By("top.s.a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(vpi_get(vpiType, a), vpiArrayVar);
  EXPECT_EQ(vpi_get(vpiSize, a), 2);
  vpiHandle first = vpi_handle_by_index(a, 0);
  ASSERT_NE(first, nullptr);
  EXPECT_EQ(vpi_get(vpiType, first), vpiReg);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, first)), VpiObjectOf(a));
  EXPECT_EQ(IntOf(first), 3);
  EXPECT_EQ(IntOf(vpi_handle_by_index(a, 1)), 9);
}

TEST_F(VariablesOfARun, AMultidimensionalArrayMemberHasSubarrays) {
  Run("module top; struct { logic [3:0] a[2][3]; } s; endmodule\n");
  vpiHandle a = By("top.s.a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(vpi_get(vpiType, a), vpiArrayVar);
  EXPECT_EQ(vpi_get(vpiSize, a), 2);
  vpiHandle row = vpi_handle_by_index(a, 1);
  ASSERT_NE(row, nullptr);
  EXPECT_EQ(vpi_get(vpiType, row), vpiArrayVar);
  EXPECT_EQ(vpi_get(vpiSize, row), 3);
  PLI_INT32 indices[] = {1, 2};
  vpiHandle element = vpi_handle_by_multi_index(a, 2, indices);
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(vpi_get(vpiType, element), vpiReg);
  EXPECT_EQ(vpi_get(vpiSize, element), 4);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, element)), VpiObjectOf(row));
}

TEST_F(VariablesOfARun, APackagesVariablesHaveTheKindsTheirTypesMake) {
  Run("interface bus; endinterface\n"
      "package pkg;\n"
      "  typedef int t;\n"
      "  int pv; real pr; virtual bus vif; t tv; int pa[2]; event pe[2];\n"
      "  const int pc = 1;\n"
      "  struct packed { logic [3:0] a; } ps = 4'd5;\n"
      "endpackage\n"
      "module top; endmodule\n");
  vpiHandle pkg = By("pkg");
  ASSERT_NE(pkg, nullptr);
  const auto kKindOf = [pkg](const char* name) {
    return vpi_get(vpiType, Named(vpiVariables, pkg, name));
  };
  EXPECT_EQ(kKindOf("pv"), vpiIntVar);
  EXPECT_EQ(kKindOf("pr"), vpiRealVar);
  EXPECT_EQ(kKindOf("vif"), vpiVirtualInterfaceVar);
  EXPECT_EQ(kKindOf("tv"), vpiIntVar);
  EXPECT_EQ(kKindOf("pa"), vpiArrayVar);
  EXPECT_EQ(vpi_get(vpiType, Named(vpiNamedEventArray, pkg, "pe")),
            vpiNamedEventArray);
  EXPECT_EQ(vpi_get(vpiConstantVariable, Named(vpiVariables, pkg, "pc")), 1);
  EXPECT_EQ(vpi_get(vpiConstantVariable, Named(vpiVariables, pkg, "pv")), 0);
  vpiHandle ps = Named(vpiVariables, pkg, "ps");
  EXPECT_EQ(vpi_get(vpiType, ps), vpiStructVar);
  EXPECT_EQ(vpi_get(vpiPacked, ps), 1);
  EXPECT_EQ(IntOf(ps), 5);
}

TEST_F(VariablesOfARun, TheCompilationUnitsVariablesHaveTheirTypesKinds) {
  Run("int g; real r;\n"
      "module top; endmodule\n");
  vpiHandle unit = Named(vpiPackage, nullptr, "$unit");
  ASSERT_NE(unit, nullptr);
  EXPECT_EQ(vpi_get(vpiType, Named(vpiVariables, unit, "g")), vpiIntVar);
  EXPECT_EQ(vpi_get(vpiType, Named(vpiVariables, unit, "r")), vpiRealVar);
}

TEST_F(VariablesOfARun, AQualifiedTypedefsVariableHasItsKindWhereverDeclared) {
  Run("package a; typedef int t; endpackage\n"
      "package b; a::t pv; endpackage\n"
      "a::t g;\n"
      "function automatic void uf(); a::t uv; endfunction\n"
      "module top;\n"
      "  a::t mv;\n"
      "  task run; a::t tv; endtask\n"
      "  initial begin : blk a::t bv; end\n"
      "endmodule\n");
  vpiHandle unit = Named(vpiPackage, nullptr, "$unit");
  ASSERT_NE(unit, nullptr);
  const auto kKindOf = [](vpiHandle scope, const char* name) {
    return vpi_get(vpiType, Named(vpiVariables, scope, name));
  };
  EXPECT_EQ(vpi_get(vpiType, By("top.mv")), vpiIntVar);
  EXPECT_EQ(kKindOf(By("b"), "pv"), vpiIntVar);
  EXPECT_EQ(kKindOf(unit, "g"), vpiIntVar);
  EXPECT_EQ(kKindOf(Named(vpiTaskFunc, unit, "uf"), "uv"), vpiIntVar);
  EXPECT_EQ(kKindOf(Named(vpiTaskFunc, By("top"), "run"), "tv"), vpiIntVar);
  EXPECT_EQ(kKindOf(By("top.blk"), "bv"), vpiIntVar);
}

TEST_F(VariablesOfARun, APackageTasksBlockVariableHasItsTypedefsKind) {
  Run("package pkg;\n"
      "  typedef int t;\n"
      "  task run; t hv; begin : blk t bv; end endtask\n"
      "endpackage\n"
      "module top; endmodule\n");
  vpiHandle run = Named(vpiTaskFunc, By("pkg"), "run");
  ASSERT_NE(run, nullptr);
  EXPECT_EQ(vpi_get(vpiType, Named(vpiVariables, run, "hv")), vpiIntVar);
  EXPECT_EQ(
      vpi_get(vpiType, Named(vpiVariables, vpi_handle(vpiStmt, run), "bv")),
      vpiIntVar);
}

TEST_F(VariablesOfARun, APackagesVariablesAreSignedScalarOrVectorAsDeclared) {
  Run("package pkg;\n"
      "  typedef logic [3:0] nib_t;\n"
      "  int pv; logic sl; logic signed [3:0] sv; bit [3:0] uv; nib_t nv;\n"
      "endpackage\n"
      "int g;\n"
      "module top; endmodule\n");
  vpiHandle pkg = By("pkg");
  ASSERT_NE(pkg, nullptr);
  const auto kOf = [pkg](int property, const char* name) {
    return vpi_get(property, Named(vpiVariables, pkg, name));
  };
  EXPECT_EQ(kOf(vpiSigned, "pv"), 1);
  EXPECT_EQ(kOf(vpiVector, "pv"), 1);
  EXPECT_EQ(kOf(vpiScalar, "pv"), 0);
  EXPECT_EQ(kOf(vpiScalar, "sl"), 1);
  EXPECT_EQ(kOf(vpiVector, "sl"), 0);
  EXPECT_EQ(kOf(vpiSigned, "sv"), 1);
  EXPECT_EQ(kOf(vpiVector, "sv"), 1);
  EXPECT_EQ(kOf(vpiSigned, "uv"), 0);
  EXPECT_EQ(kOf(vpiVector, "nv"), 1);
  EXPECT_EQ(kOf(vpiScalar, "nv"), 0);
  vpiHandle g = Named(vpiVariables, Named(vpiPackage, nullptr, "$unit"), "g");
  EXPECT_EQ(vpi_get(vpiSigned, g), 1);
  EXPECT_EQ(vpi_get(vpiVector, g), 1);
}

TEST_F(VariablesOfARun, APackagesArrayVarsReportTheirArrayTypeAndSize) {
  Run("package pkg;\n"
      "  parameter int N = 3;\n"
      "  int pa[4]; int pn[N]; int pr[1:2][3]; int pd[]; int pq[$];\n"
      "  int pm[string];\n"
      "endpackage\n"
      "module top; endmodule\n");
  vpiHandle pkg = By("pkg");
  ASSERT_NE(pkg, nullptr);
  const auto kOf = [pkg](int property, const char* name) {
    return vpi_get(property, Named(vpiVariables, pkg, name));
  };
  EXPECT_EQ(kOf(vpiArrayType, "pa"), vpiStaticArray);
  EXPECT_EQ(kOf(vpiSize, "pa"), 4);
  EXPECT_EQ(kOf(vpiSize, "pn"), 3);
  EXPECT_EQ(kOf(vpiSize, "pr"), 2);
  EXPECT_EQ(kOf(vpiArrayType, "pd"), vpiDynamicArray);
  EXPECT_EQ(kOf(vpiArrayType, "pq"), vpiQueueArray);
  EXPECT_EQ(kOf(vpiArrayType, "pm"), vpiAssocArray);
}

TEST_F(VariablesOfARun, ANestedModulesVariableReachesItsTypedefsTypespec) {
  Run("module top;\n"
      "  module inner; typedef bit [3:0] nib_t; nib_t v; endmodule\n"
      "  inner i();\n"
      "endmodule\n");
  vpiHandle typespec = vpi_handle(vpiTypespec, By("top.i.v"));
  ASSERT_NE(typespec, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, typespec), "nib_t");
}

}  // namespace
}  // namespace delta
