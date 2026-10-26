#include <gtest/gtest.h>

#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.17 Variables, read off the VPI model a run builds from an elaborated
// design: the objects and properties detail by detail gives a variable, its
// members, its elements and the selects into it.

class VariablesOfARun : public VpiDesignRun {
 protected:
  // The value of `obj` read as an integer.
  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }
};

// D12: a variable whose type is a typedef of a packed logic vector has a var
// bit per bit, as one declared with the vector's dimension written out does
// (#7349).
TEST_F(VariablesOfARun, ATypedefPackedVectorVariableHasBits) {
  Run("typedef logic [2:0] t3;\n"
      "module top; t3 a; logic [2:0] b; endmodule\n");
  EXPECT_EQ(ObjectsOf(vpiBit, By("top.a")).size(), 3U);
  EXPECT_EQ(ObjectsOf(vpiBit, By("top.b")).size(), 3U);
}

// An element of an array of a built-in type other than logic is a variable of
// that type, an int var of `int a[4]`, so the array is no memory; an element of
// a logic array stays a reg (#6996).
TEST_F(VariablesOfARun, AnArrayElementIsAVariableOfItsElementType) {
  Run("module top; int a[4]; byte c[2]; logic [3:0] m[2]; endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_index(By("top.a"), 0)), vpiIntVar);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_index(By("top.c"), 1)), vpiByteVar);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_index(By("top.m"), 0)), vpiReg);
  EXPECT_EQ(vpi_get(vpiIsMemory, By("top.a")), 0);
  EXPECT_EQ(vpi_get(vpiIsMemory, By("top.m")), 1);
}

// A variable reaches the ports it connects as a net does: a variable port's
// own variable its port through vpiPorts, and a variable connected to an
// instance's port that port through vpiPortInst (#6997).
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

// An array var reaches the var selects of it, each reaching the array back
// through vpiParent, while an index still selects the array's element (#6998).
TEST_F(VariablesOfARun, AnArrayVarReachesItsVarSelects) {
  Run("module top; int a[4]; int i; initial a[i] = 1; endmodule\n");
  std::vector<vpiHandle> selects = ObjectsOf(vpiVarSelect, By("top.a"));
  ASSERT_EQ(selects.size(), 1U);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, selects[0])),
            VpiObjectOf(By("top.a")));
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_index(By("top.a"), 0)), vpiIntVar);
}

// A variable of a built-in type relates to a typespec of that type, which
// §37.25 detail 1 leaves without a name (#6999).
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

// D15, D16 and D22: a class property reports the randomization type it was
// declared with, and any other variable vpiNotRand; a random property is
// randomized until rand_mode() turns it off (#7000, #7001).
TEST_F(VariablesOfARun, AVariableReportsItsRandomization) {
  Run("module top;\n"
      "  class C; rand int r; randc bit [1:0] k; rand int off; int n;\n"
      "  endclass\n"
      "  C c = new; int x;\n"
      "  initial c.off.rand_mode(0);\n"
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
}

// D17: a member of a structure variable is a struct union member, and a
// variable of the module is not (#7002).
TEST_F(VariablesOfARun, AStructMemberIsAStructUnionMember) {
  Run("module top; struct { int i1; } s; int x; endmodule\n");
  EXPECT_EQ(vpi_get(vpiStructUnionMember, By("top.s.i1")), 1);
  EXPECT_EQ(vpi_get(vpiStructUnionMember, By("top.x")), 0);
}

// A variable declared const, of a module or a class, is a constant variable,
// and one declared without is not (#7003).
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

// D24: a property reached through a class object reports the visibility it
// was declared with, as one reached through the class defn does (#7011).
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

// D5 and D10: a var select reaches its index through vpi_handle, a select
// through another reaches the indices of both, its own first, and a select
// of an element is as wide as the element (#7004, #7005, #7007).
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

// D8: a variable declared with an initialization expression reaches it
// through vpiExpr, and one declared without reaches nothing (#7006).
TEST_F(VariablesOfARun, AVariableReachesItsInitializationExpression) {
  Run("module top; int k = 2; int x = k + 5; int y; endmodule\n");
  vpiHandle init = vpi_handle(vpiExpr, By("top.x"));
  ASSERT_NE(init, nullptr);
  EXPECT_EQ(vpi_get(vpiType, init), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, init), vpiAddOp);
  EXPECT_EQ(vpi_handle(vpiExpr, By("top.y")), nullptr);
}

// D11 with §37.26: a packed structure variable is packed and its value is
// read, where an unpacked one is not packed (#7008).
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

// D11: an array var and a class var have no value, so reading either is
// refused with an error and leaves the value buffer as it was (#7009).
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

// D11: having no value, an array var or a class var takes none put to it
// either, the put being refused with an error (#7851).
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

// D20: a member of a structure and an element of an array are scalars or
// vectors as a variable of their type is (#7010).
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

// D25: a non-static data member of a class has no full name, reached through
// a class object as through its class defn, though vpi_handle_by_name still
// finds it by one (§37.33 detail 9) (#7012).
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

// D3 and D28's example: a member of a structure type has members of its own,
// `str1.inner1.j1`, holding its bits of the outermost structure (#7013).
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

// D12 and D28's example: a packed member of a structure has a var bit per bit,
// `str1.vec[5]`, of its packed dimensions or a packed structure's implicit
// one, each holding its bit of the outermost structure (#7014).
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

// D26: an element of an array of structures is a structure variable with a
// member per field, each reaching the element as its parent and holding its
// bits of the element (#7015).
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

// D28: a variable decompiles to its name with the struct and union vars it is
// a member of before it, a bit with its index as well (#7016).
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

// D2, D18 and D26: a member of a structure declared with an unpacked dimension
// is an array var, with an element per index that is a variable of the
// member's type holding its bits of the structure (#7357).
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

// D2, D18 and D26: a member of a structure declared with two unpacked
// dimensions is an array var whose subarrays are array vars of their own, each
// holding an element per index of the second dimension (#7358).
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

}  // namespace
}  // namespace delta
