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

class VariableRelationsOfARun : public VpiDesignRun {
 protected:
  static VpiObject* ParentOf(vpiHandle obj) {
    return obj == nullptr ? nullptr : VpiObjectOf(vpi_handle(vpiParent, obj));
  }

  static vpiHandle ElementOf(vpiHandle array, std::vector<PLI_INT32> indices) {
    if (array == nullptr) return nullptr;
    return vpi_handle_by_multi_index(
        array, static_cast<PLI_INT32>(indices.size()), indices.data());
  }

  static VpiObject* ReachedBy(int relation, const char* name) {
    vpiHandle obj = By(name);
    return obj == nullptr ? nullptr : VpiObjectOf(vpi_handle(relation, obj));
  }

  static std::vector<vpiHandle> LhsOfInitialAssigns() {
    std::vector<vpiHandle> lhs;
    for (vpiHandle proc : ObjectsOf(vpiProcess, By("top"))) {
      for (vpiHandle assign : ObjectsOf(vpiStmt, vpi_handle(vpiStmt, proc))) {
        lhs.push_back(vpi_handle(vpiLhs, assign));
      }
    }
    return lhs;
  }

  static std::string Str(int property, vpiHandle obj) {
    const char* text = obj == nullptr ? nullptr : vpi_get_str(property, obj);
    return text == nullptr ? "<null>" : text;
  }

  static bool RangeIsEmpty(vpiHandle range) {
    return range != nullptr && vpi_handle(vpiLeftRange, range) == nullptr &&
           vpi_handle(vpiRightRange, range) == nullptr &&
           vpi_get(vpiSize, range) == 0;
  }

  static int BoundOf(int relation, vpiHandle var) {
    vpiHandle bound = vpi_handle(relation, var);
    return bound == nullptr ? -1 : IntegerOf(bound);
  }
};

TEST_F(VariableRelationsOfARun,
       DISABLED_AMultidimensionalElementHasTheWholeArrayAsParent) {
  Run("module top; logic [1:0][2:3] mda [4:6][7:8]; endmodule\n");
  vpiHandle mda = By("top.mda");
  vpiHandle element = ElementOf(mda, {6, 8});
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(ParentOf(element), VpiObjectOf(mda));
}

TEST_F(VariableRelationsOfARun,
       DISABLED_AMultidimensionalArrayMembersElementHasTheMemberAsParent) {
  Run("module top; struct { logic [3:0] a[2][3]; } s; endmodule\n");
  vpiHandle a = By("top.s.a");
  vpiHandle element = ElementOf(a, {1, 2});
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(ParentOf(element), VpiObjectOf(a));
}

TEST_F(VariableRelationsOfARun,
       DISABLED_APackedSelectOfAnElementHasTheElementAsParent) {
  Run("module top; logic [1:0][2:3] mda [4:6][7:8]; endmodule\n");
  vpiHandle element = ElementOf(By("top.mda"), {6, 8});
  ASSERT_NE(element, nullptr);
  vpiHandle subvector = vpi_handle_by_index(element, 1);
  ASSERT_NE(subvector, nullptr);
  vpiHandle bit = vpi_handle_by_index(subvector, 3);
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(ParentOf(subvector), VpiObjectOf(element));
  EXPECT_EQ(ParentOf(bit), VpiObjectOf(element));
}

TEST_F(VariableRelationsOfARun,
       DISABLED_AMemberChainWalksOneQualifyingPrefixAtATime) {
  Run("module top;\n"
      "  struct { integer i1; logic [1:0][2:3] bvec [4:5]; } spa "
      "[9:11][12:13];\n"
      "endmodule\n");
  vpiHandle spa = By("top.spa");
  vpiHandle element = ElementOf(spa, {9, 12});
  ASSERT_NE(element, nullptr);
  vpiHandle bvec = Named(vpiMember, element, "bvec");
  ASSERT_NE(bvec, nullptr);
  vpiHandle bvec4 = vpi_handle_by_index(bvec, 4);
  ASSERT_NE(bvec4, nullptr);
  vpiHandle bvec40 = vpi_handle_by_index(bvec4, 0);
  ASSERT_NE(bvec40, nullptr);
  EXPECT_EQ(ParentOf(bvec40), VpiObjectOf(bvec4));
  EXPECT_EQ(ParentOf(bvec4), VpiObjectOf(bvec));
  EXPECT_EQ(ParentOf(bvec), VpiObjectOf(element));
  EXPECT_EQ(ParentOf(element), VpiObjectOf(spa));
  EXPECT_EQ(ParentOf(spa), nullptr);
}

TEST_F(VariableRelationsOfARun, AModuleVariableWithNoPrefixHasNoParent) {
  Run("module top; logic v; int n; endmodule\n");
  ASSERT_NE(By("top.v"), nullptr);
  EXPECT_EQ(ParentOf(By("top.v")), nullptr);
  EXPECT_EQ(ParentOf(By("top.n")), nullptr);
}

TEST_F(VariableRelationsOfARun,
       DISABLED_AClassMemberHasItsClassVarAsParentOnlyWhenReachedThroughIt) {
  Run("module top; class C; int x; endclass C c = new; endmodule\n");
  vpiHandle through_var = By("top.c.x");
  ASSERT_NE(through_var, nullptr);
  EXPECT_EQ(ParentOf(through_var), VpiObjectOf(By("top.c")));
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.c"));
  ASSERT_NE(obj, nullptr);
  vpiHandle through_obj = Named(vpiVariables, obj, "x");
  ASSERT_NE(through_obj, nullptr);
  EXPECT_EQ(ParentOf(through_obj), nullptr);
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(defn, nullptr);
  vpiHandle through_defn = Named(vpiVariables, defn, "x");
  ASSERT_NE(through_defn, nullptr);
  EXPECT_EQ(ParentOf(through_defn), nullptr);
}

std::string ConnectionsDesign() {
  return "module top(input var logic d, input clk, output logic o,\n"
         "           output wire y);\n"
         "  logic v, u, n;\n"
         "  and g(y, v, clk);\n"
         "  assign u = v;\n"
         "  specify (clk => o) = 1; $setup(d, posedge clk, 1); endspecify\n"
         "endmodule\n";
}

TEST_F(VariableRelationsOfARun,
       DISABLED_AVariableAGateReadsIteratesItsPrimTerm) {
  Run(ConnectionsDesign());
  const std::vector<vpiHandle> kTerms = ObjectsOf(vpiPrimTerm, By("top.v"));
  ASSERT_EQ(kTerms.size(), 1U);
  EXPECT_EQ(vpi_get(vpiType, kTerms[0]), vpiPrimTerm);
  EXPECT_EQ(vpi_iterate(vpiPrimTerm, By("top.n")), nullptr);
}

TEST_F(VariableRelationsOfARun, AVariableAnAssignWritesOrReadsIteratesIt) {
  Run(ConnectionsDesign());
  for (const char* name : {"top.u", "top.v"}) {
    const std::vector<vpiHandle> kAssigns = ObjectsOf(vpiContAssign, By(name));
    ASSERT_EQ(kAssigns.size(), 1U) << name;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, kAssigns[0])),
              VpiObjectOf(By("top.u")))
        << name;
  }
  EXPECT_EQ(vpi_iterate(vpiContAssign, By("top.n")), nullptr);
}

TEST_F(VariableRelationsOfARun,
       DISABLED_APathDestinationVariableIteratesItsPathTerm) {
  Run(ConnectionsDesign());
  const std::vector<vpiHandle> kTerms = ObjectsOf(vpiPathTerm, By("top.o"));
  ASSERT_EQ(kTerms.size(), 1U);
  EXPECT_EQ(vpi_get(vpiType, kTerms[0]), vpiPathTerm);
  EXPECT_EQ(vpi_iterate(vpiPathTerm, By("top.n")), nullptr);
}

TEST_F(VariableRelationsOfARun,
       DISABLED_ATimingCheckedVariableIteratesItsTchkTerm) {
  Run(ConnectionsDesign());
  const std::vector<vpiHandle> kTerms = ObjectsOf(vpiTchkTerm, By("top.d"));
  ASSERT_EQ(kTerms.size(), 1U);
  EXPECT_EQ(vpi_get(vpiType, kTerms[0]), vpiTchkTerm);
  EXPECT_EQ(vpi_iterate(vpiTchkTerm, By("top.n")), nullptr);
}

std::string ScopesDesign() {
  return "interface bus; logic v; endinterface\n"
         "program prg; int v; endprogram\n"
         "module sub; int v; endmodule\n"
         "module top; sub m1(); bus i(); prg p();\n"
         "  initial begin : b int x; end\n"
         "  if (1) begin : g int v; end\n"
         "endmodule\n";
}

TEST_F(VariableRelationsOfARun, AVariablesModuleIsTheModuleAroundIt) {
  Run(ScopesDesign());
  ASSERT_NE(By("top.m1.v"), nullptr);
  EXPECT_EQ(ReachedBy(vpiModule, "top.m1.v"), VpiObjectOf(By("top.m1")));
  ASSERT_NE(By("top.b.x"), nullptr);
  EXPECT_EQ(ReachedBy(vpiModule, "top.b.x"), VpiObjectOf(By("top")));
  ASSERT_NE(By("top.g.v"), nullptr);
  EXPECT_EQ(ReachedBy(vpiModule, "top.g.v"), VpiObjectOf(By("top")));
}

TEST_F(VariableRelationsOfARun, AVariablesInstanceIsTheInstanceAroundIt) {
  Run(ScopesDesign());
  ASSERT_NE(By("top.m1.v"), nullptr);
  EXPECT_EQ(ReachedBy(vpiInstance, "top.m1.v"), VpiObjectOf(By("top.m1")));
  ASSERT_NE(By("top.i.v"), nullptr);
  EXPECT_EQ(ReachedBy(vpiInstance, "top.i.v"), VpiObjectOf(By("top.i")));
  ASSERT_NE(By("top.p.v"), nullptr);
  EXPECT_EQ(ReachedBy(vpiInstance, "top.p.v"), VpiObjectOf(By("top.p")));
}

std::string NamesDesign() {
  return "module top;\n"
         "  bit [7:0] arr1 [1:4][9:15];\n"
         "  struct { integer i1; logic [1:4] vec [5:8];\n"
         "    struct { shortint j1; byte b1; } inner1; } str1;\n"
         "  class cdef; int cvInt; endclass\n"
         "  cdef cv = new;\n"
         "endmodule\n";
}

TEST_F(VariableRelationsOfARun, ANestedMemberIsNamedWithoutAndFullyWithPrefix) {
  Run(NamesDesign());
  vpiHandle j1 = By("top.str1.inner1.j1");
  ASSERT_NE(j1, nullptr);
  EXPECT_EQ(Str(vpiName, j1), "j1");
  EXPECT_EQ(Str(vpiFullName, j1), "top.str1.inner1.j1");
  EXPECT_EQ(Str(vpiDecompile, j1), "str1.inner1.j1");
}

TEST_F(VariableRelationsOfARun, DISABLED_AnIndexedObjectsNamesCarryItsIndices) {
  Run(NamesDesign());
  vpiHandle element = ElementOf(By("top.arr1"), {1, 9});
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(Str(vpiName, element), "arr1[1][9]");
  EXPECT_EQ(Str(vpiDecompile, element), "arr1[1][9]");
  EXPECT_EQ(Str(vpiFullName, element), "top.arr1[1][9]");
  vpiHandle vec5 = vpi_handle_by_index(By("top.str1.vec"), 5);
  ASSERT_NE(vec5, nullptr);
  EXPECT_EQ(Str(vpiName, vec5), "vec[5]");
  EXPECT_EQ(Str(vpiDecompile, vec5), "str1.vec[5]");
  EXPECT_EQ(Str(vpiFullName, vec5), "top.str1.vec[5]");
}

TEST_F(VariableRelationsOfARun,
       DISABLED_AClassVarsMemberDecompilesWithTheClassVar) {
  Run(NamesDesign());
  vpiHandle member = By("top.cv.cvInt");
  ASSERT_NE(member, nullptr);
  EXPECT_EQ(Str(vpiName, member), "cvInt");
  EXPECT_EQ(Str(vpiDecompile, member), "cv.cvInt");
  EXPECT_EQ(Str(vpiFullName, member), "<null>");
}

TEST_F(VariableRelationsOfARun, AMemberIsFoundByItsDecompileBelowTheTop) {
  Run("module sub;\n"
      "  struct { struct { int j1; } inner1; } str1;\n"
      "endmodule\n"
      "module top; sub u(); endmodule\n");
  vpiHandle full = By("top.u.str1.inner1.j1");
  ASSERT_NE(full, nullptr);
  vpiHandle scope = By("top.u");
  ASSERT_NE(scope, nullptr);
  vpiHandle scoped = vpi_handle_by_name(VpiText("str1.inner1.j1"), scope);
  ASSERT_NE(scoped, nullptr);
  EXPECT_EQ(VpiObjectOf(scoped), VpiObjectOf(full));
  EXPECT_EQ(Str(vpiFullName, scoped), "top.u.str1.inner1.j1");
}

TEST_F(VariableRelationsOfARun, AnArrayVarIteratesItsElementsAsRegs) {
  Run("module top; int a[4]; logic l[1:3]; endmodule\n");
  const std::vector<vpiHandle> kInts = ObjectsOf(vpiReg, By("top.a"));
  ASSERT_EQ(kInts.size(), 4U);
  for (int index = 0; index < 4; ++index) {
    EXPECT_EQ(vpi_get(vpiType, kInts[index]), vpiIntVar);
    EXPECT_EQ(VpiObjectOf(kInts[index]),
              VpiObjectOf(vpi_handle_by_index(By("top.a"), index)));
  }
  const std::vector<vpiHandle> kLogics = ObjectsOf(vpiReg, By("top.l"));
  ASSERT_EQ(kLogics.size(), 3U);
  for (int index = 1; index <= 3; ++index) {
    EXPECT_EQ(vpi_get(vpiType, kLogics[index - 1]), vpiLogicVar);
    EXPECT_EQ(VpiObjectOf(kLogics[index - 1]),
              VpiObjectOf(vpi_handle_by_index(By("top.l"), index)));
  }
}

TEST_F(VariableRelationsOfARun, AnArrayIteratesOnlyItsOuterVarSelect) {
  Run("module top; logic m[2][2]; int i; initial m[i][0] = 1; endmodule\n");
  EXPECT_EQ(NamesOf(vpiVarSelect, By("top.m")),
            (std::vector<std::string>{"m[i]"}));
}

TEST_F(VariableRelationsOfARun, ASelectAtAVaryingIndexIsNoConstantSelect) {
  Run("module top; int a[4]; logic [3:0] v; int i;\n"
      "  initial begin a[i] = 1; v[i] = 1'b1; end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kLhs = LhsOfInitialAssigns();
  ASSERT_EQ(kLhs.size(), 2U);
  ASSERT_NE(kLhs[0], nullptr);
  EXPECT_EQ(vpi_get(vpiType, kLhs[0]), vpiVarSelect);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kLhs[0]), 0);
  ASSERT_NE(kLhs[1], nullptr);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kLhs[1]), 0);
  EXPECT_EQ(vpi_get(vpiConstantSelect, vpi_handle_by_index(By("top.a"), 2)), 1);
}

TEST_F(VariableRelationsOfARun,
       ADynamicOrAssociativeElementIsNoConstantSelect) {
  Run("module top; int d[]; int aa[int];\n"
      "  initial begin d = new[3]; aa[5] = 1; end\n"
      "endmodule\n");
  vpiHandle dynamic = vpi_handle_by_index(By("top.d"), 1);
  ASSERT_NE(dynamic, nullptr);
  EXPECT_EQ(vpi_get(vpiConstantSelect, dynamic), 0);
  vpiHandle assoc = vpi_handle_by_index(By("top.aa"), 5);
  ASSERT_NE(assoc, nullptr);
  EXPECT_EQ(vpi_get(vpiConstantSelect, assoc), 0);
}

TEST_F(VariableRelationsOfARun, AMemberOfAConstantlySelectedElementIsConstant) {
  Run("typedef struct { logic [7:0] bvec; int n; } s_t;\n"
      "module top; s_t spa[2][3]; endmodule\n");
  vpiHandle element = ElementOf(By("top.spa"), {1, 2});
  ASSERT_NE(element, nullptr);
  vpiHandle bvec = Named(vpiMember, element, "bvec");
  ASSERT_NE(bvec, nullptr);
  EXPECT_EQ(vpi_get(vpiConstantSelect, bvec), 1);
}

TEST_F(VariableRelationsOfARun, DISABLED_AClassVarsMemberIsNoConstantSelect) {
  Run("module top; class C; int x; endclass C c = new; endmodule\n");
  vpiHandle member = By("top.c.x");
  ASSERT_NE(member, nullptr);
  EXPECT_EQ(vpi_get(vpiConstantSelect, member), 0);
  EXPECT_EQ(vpi_get(vpiConstantSelect, By("top.c")), 1);
}

TEST_F(VariableRelationsOfARun, AVariableSizedDimensionPastTheFirstIsEmpty) {
  Run("module top; int a[2][$]; int b[2][]; int c[2][string]; int d[int];\n"
      "endmodule\n");
  for (const char* name : {"top.a", "top.b", "top.c"}) {
    const std::vector<vpiHandle> kRanges = ObjectsOf(vpiRange, By(name));
    ASSERT_EQ(kRanges.size(), 2U) << name;
    EXPECT_EQ(IntegerOf(vpi_handle(vpiLeftRange, kRanges[0])), 0) << name;
    EXPECT_EQ(IntegerOf(vpi_handle(vpiRightRange, kRanges[0])), 1) << name;
    EXPECT_TRUE(RangeIsEmpty(kRanges[1])) << name;
  }
  const std::vector<vpiHandle> kOnly = ObjectsOf(vpiRange, By("top.d"));
  ASSERT_EQ(kOnly.size(), 1U);
  EXPECT_TRUE(RangeIsEmpty(kOnly[0]));
}

TEST_F(VariableRelationsOfARun,
       DISABLED_APackedArrayOfAggregatesHasOnlyItsOwnRanges) {
  Run("typedef struct packed { logic [3:0] f; } ps_t;\n"
      "typedef union packed { logic [3:0] f; bit [3:0] g; } pu_t;\n"
      "typedef enum logic [2:0] { A, B } e_t;\n"
      "module top; ps_t [1:0] pss; pu_t [2:0] pus; e_t [4:1] pes; endmodule\n");
  EXPECT_EQ(BoundsOf(By("top.pss")), (std::vector<int>{1, 0}));
  EXPECT_EQ(BoundsOf(By("top.pus")), (std::vector<int>{2, 0}));
  EXPECT_EQ(BoundsOf(By("top.pes")), (std::vector<int>{4, 1}));
}

TEST_F(VariableRelationsOfARun, AnArrayWithNoElementsHasNoBounds) {
  Run("module top; int eq[$]; int ed[]; int ea[int]; endmodule\n");
  for (const char* name : {"top.eq", "top.ed", "top.ea"}) {
    ASSERT_NE(By(name), nullptr) << name;
    EXPECT_EQ(vpi_handle(vpiLeftRange, By(name)), nullptr) << name;
    EXPECT_EQ(vpi_handle(vpiRightRange, By(name)), nullptr) << name;
  }
}

TEST_F(VariableRelationsOfARun,
       AFilledQueueOrDynamicArrayIsBoundByItsElements) {
  Run("module top; int nq[$]; int nd[];\n"
      "  initial begin nq = '{5, 6, 7}; nd = new[2]; end\n"
      "endmodule\n");
  EXPECT_EQ(BoundOf(vpiLeftRange, By("top.nq")), 0);
  EXPECT_EQ(BoundOf(vpiRightRange, By("top.nq")), 2);
  EXPECT_EQ(BoundOf(vpiLeftRange, By("top.nd")), 0);
  EXPECT_EQ(BoundOf(vpiRightRange, By("top.nd")), 1);
}

}  // namespace
}  // namespace delta
