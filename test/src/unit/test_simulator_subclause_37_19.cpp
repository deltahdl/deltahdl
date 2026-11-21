#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(VariableSelectModel, ConstantSelectRequiresAllThreeConditions) {
  VpiVarSelectConstantSelectQuery all_true;
  all_true.all_indices_constant = true;
  all_true.parent_is_unpacked_static_array = true;
  all_true.parent_constant_select = true;
  EXPECT_TRUE(VpiVarSelectConstantSelect(all_true));

  VpiVarSelectConstantSelectQuery q1 = all_true;
  q1.all_indices_constant = false;
  EXPECT_FALSE(VpiVarSelectConstantSelect(q1));

  VpiVarSelectConstantSelectQuery q2 = all_true;
  q2.parent_is_unpacked_static_array = false;
  EXPECT_FALSE(VpiVarSelectConstantSelect(q2));

  VpiVarSelectConstantSelectQuery q3 = all_true;
  q3.parent_constant_select = false;
  EXPECT_FALSE(VpiVarSelectConstantSelect(q3));
}

class VariableSelectObject : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    array_.type = vpiArrayVar;
    array_.array_type = vpiStaticArray;
    index_.type = vpiConstant;
    select_.type = vpiVarSelect;
    select_.parent = &array_;
    select_.children = {&index_};
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  std::vector<vpiHandle> ScanAll(vpiHandle it) {
    std::vector<vpiHandle> seen;
    if (it == nullptr) return seen;
    while (vpiHandle h = vpi_scan(it)) seen.push_back(h);
    return seen;
  }

  VpiObject array_;
  VpiObject index_;
  VpiObject select_;
  VpiContext ctx_;
};

TEST_F(VariableSelectObject, AConstantIndexIntoAStaticArrayIsAConstantSelect) {
  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&select_)), 1);
}

TEST_F(VariableSelectObject, ANonConstantIndexMakesTheSelectNonConstant) {
  index_.type = vpiOperation;

  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&select_)), 0);
}

TEST_F(VariableSelectObject, ADynamicallyBoundedParentMakesItNonConstant) {
  array_.array_type = vpiDynamicArray;

  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&select_)), 0);
}

TEST_F(VariableSelectObject, AQueueOrAssociativeParentMakesItNonConstant) {
  array_.array_type = vpiQueueArray;
  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&select_)), 0);
  array_.array_type = vpiAssocArray;
  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&select_)), 0);
}

TEST_F(VariableSelectObject, AnAutomaticParentMakesItNonConstant) {
  array_.automatic = true;

  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&select_)), 0);
}

TEST_F(VariableSelectObject,
       DISABLED_ASelectThroughAConstantSelectIsAConstantSelect) {
  VpiObject outer_index;
  outer_index.type = vpiConstant;
  VpiObject outer;
  outer.type = vpiVarSelect;
  outer.parent = &array_;
  outer.children = {&outer_index};

  select_.parent = &outer;

  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&outer)), 1);
  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&select_)), 1);
}

TEST_F(VariableSelectObject, TheArrayIsAnsweredByTheVariablesRule) {
  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&array_)), 1);
}

TEST_F(VariableSelectObject,
       TheIndexRelationReachesTheSelectsIndexExpressions) {
  VpiObject second;
  second.type = vpiOperation;
  select_.children = {&index_, &second};

  std::vector<vpiHandle> seen =
      ScanAll(vpi_iterate(vpiIndex, VpiHandleOf(&select_)));
  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &index_);
  EXPECT_EQ(VpiObjectOf(seen[1]), &second);
}

TEST_F(VariableSelectObject, ATypespecIsTheArraysUnwoundOncePerSelect) {
  EXPECT_EQ(vpi_handle(vpiTypespec, VpiHandleOf(&select_)), nullptr);

  VpiObject element_typespec;
  element_typespec.type = vpiIntTypespec;
  VpiObject array_typespec;
  array_typespec.type = vpiArrayTypespec;
  array_typespec.inner_typespec = &element_typespec;
  array_.children.push_back(&array_typespec);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTypespec, VpiHandleOf(&select_))),
            &element_typespec);

  VpiObject deeper;
  deeper.type = vpiVarSelect;
  deeper.parent = &select_;
  EXPECT_EQ(vpi_handle(vpiTypespec, VpiHandleOf(&deeper)), nullptr);
}

class VarSelectsOfARun : public VpiDesignRun {
 protected:
  static std::string Design(const std::string& decls,
                            const std::string& setup) {
    return "module top; logic v [2]; " + decls +
           " wire y; logic c;\n"
           "  and g(y, v[i], c);\n"
           "  initial begin v[0] = 0; v[1] = 1; " +
           setup + " end\nendmodule\n";
  }

  static vpiHandle Select() {
    vpiHandle it =
        vpi_iterate(vpiPrimTerm, Named(vpiPrimitive, By("top"), "g"));
    if (it == nullptr) return nullptr;
    vpi_scan(it);
    vpiHandle term = vpi_scan(it);
    vpi_free_object(it);
    return term == nullptr ? nullptr : vpi_handle(vpiExpr, term);
  }

  static std::string BinOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiBinStrVal;
    vpi_get_value(obj, &value);
    return value.format == vpiBinStrVal && value.value.str != nullptr
               ? std::string(value.value.str)
               : std::string();
  }

  static std::string Str(int property, vpiHandle obj) {
    const char* text = obj == nullptr ? nullptr : vpi_get_str(property, obj);
    return text == nullptr ? std::string("<null>") : std::string(text);
  }

  static void PutInt(vpiHandle obj, int integer) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = integer;
    vpi_put_value(obj, &value, nullptr, vpiNoDelay);
  }

  static vpiHandle OnlySelectOf(vpiHandle array) {
    const std::vector<vpiHandle> kSelects = ObjectsOf(vpiVarSelect, array);
    return kSelects.size() == 1 ? kSelects[0] : nullptr;
  }

  static vpiHandle SelectOf(const std::string& array,
                            const std::string& index) {
    return Named(vpiVarSelect, By("top." + array), array + "[" + index + "]");
  }

  static void ExpectSelectOf(vpiHandle array, const std::string& index) {
    ASSERT_NE(array, nullptr) << index;
    vpiHandle select = OnlySelectOf(array);
    ASSERT_NE(select, nullptr) << Str(vpiFullName, array);
    EXPECT_EQ(vpi_get(vpiType, select), vpiVarSelect);
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, select)), VpiObjectOf(array));
  }

  static void ExpectSelectNamed(vpiHandle array, const std::string& index) {
    ASSERT_NE(array, nullptr) << index;
    vpiHandle select = OnlySelectOf(array);
    ASSERT_NE(select, nullptr) << Str(vpiFullName, array);
    EXPECT_EQ(Str(vpiName, select), Str(vpiName, array) + index);
    EXPECT_EQ(Str(vpiFullName, select), Str(vpiFullName, array) + index);
  }

  static void ExpectNamedSelectOf(vpiHandle array, const std::string& index) {
    ExpectSelectOf(array, index);
    ExpectSelectNamed(array, index);
  }

  static void ExpectSelectWidths(const std::vector<std::string>& names,
                                 const std::vector<int>& widths) {
    for (size_t at = 0; at < names.size(); ++at) {
      vpiHandle select = SelectOf(names[at], "k");
      ASSERT_NE(select, nullptr) << names[at];
      EXPECT_EQ(vpi_get(vpiSize, select), widths[at]) << names[at];
    }
  }

  static void AddLhsOf(vpiHandle stmt, std::vector<vpiHandle>* lhs) {
    if (stmt == nullptr) return;
    if (vpiHandle target = vpi_handle(vpiLhs, stmt)) {
      lhs->push_back(target);
      return;
    }
    for (vpiHandle inner : ObjectsOf(vpiStmt, stmt)) AddLhsOf(inner, lhs);
  }

  static std::vector<vpiHandle> LhsOf(vpiHandle scope) {
    std::vector<vpiHandle> lhs;
    for (vpiHandle proc : ObjectsOf(vpiProcess, scope)) {
      AddLhsOf(vpi_handle(vpiStmt, proc), &lhs);
    }
    return lhs;
  }

  static std::vector<vpiHandle> SubroutineLhsOf(const char* name) {
    std::vector<vpiHandle> lhs;
    AddLhsOf(vpi_handle(vpiStmt, Named(vpiTaskFunc, By("top"), name)), &lhs);
    return lhs;
  }

  static std::string ElementsOfM() {
    return BinOf(By("top.m[0][0]")) + BinOf(By("top.m[0][1]")) +
           BinOf(By("top.m[1][0]")) + BinOf(By("top.m[1][1]"));
  }
};

TEST_F(VarSelectsOfARun, AVaryingIndexIntoAnArrayVarIsAVarSelect) {
  Run(Design("int i;", "i = 1;"));
  vpiHandle select = Select();
  ASSERT_NE(select, nullptr);
  EXPECT_EQ(vpi_get(vpiType, select), vpiVarSelect);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, select)),
            VpiObjectOf(By("top.v")));
  EXPECT_EQ(vpi_get(vpiConstantSelect, select), 0);
  vpiHandle it = vpi_iterate(vpiIndex, select);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), VpiObjectOf(By("top.i")));
}

TEST_F(VarSelectsOfARun, AVarSelectReadsAndWritesTheElementItsIndexNames) {
  Run(Design("int i;", "i = 1;"));
  vpiHandle select = Select();
  ASSERT_NE(select, nullptr);
  EXPECT_EQ(BinOf(select), "1");
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 0;
  vpi_put_value(select, &value, nullptr, vpiNoDelay);
  EXPECT_EQ(BinOf(By("top.v[1]")), "0");
}

TEST_F(VarSelectsOfARun, AVarSelectWhoseIndexIsOutOfRangeReadsX) {
  Run(Design("int i;", "i = 5;"));
  EXPECT_EQ(BinOf(Select()), "x");
}

TEST_F(VarSelectsOfARun, AVarSelectWhoseIndexHoldsXReadsX) {
  Run(Design("integer i;", ""));
  EXPECT_EQ(BinOf(Select()), "x");
}

std::string TwoDimensional(const std::string& inner, int outer) {
  return "module top; logic m [2][2]; int i, j; wire y; logic c;\n"
         "  and g(y, m[i][" +
         inner +
         "], c);\n"
         "  initial begin m[0][0] = 0; m[1][0] = 1; j = 5; i = " +
         std::to_string(outer) + "; end\nendmodule\n";
}

TEST_F(VarSelectsOfARun, ASelectThroughAVarSelectIsAVarSelect) {
  Run(TwoDimensional("0", 1));
  vpiHandle select = Select();
  ASSERT_NE(select, nullptr);
  EXPECT_EQ(vpi_get(vpiType, select), vpiVarSelect);
  vpiHandle outer = vpi_handle(vpiParent, select);
  ASSERT_NE(outer, nullptr);
  EXPECT_EQ(vpi_get(vpiType, outer), vpiVarSelect);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, outer)),
            VpiObjectOf(By("top.m")));
  EXPECT_EQ(vpi_get(vpiConstantSelect, select), 0);
  EXPECT_EQ(BinOf(select), "1");
}

TEST_F(VarSelectsOfARun, AVarSelectIsNamedAndReachesItsElementTypespec) {
  Run(TwoDimensional("0", 1));
  vpiHandle select = Select();
  ASSERT_NE(select, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, select), "m[i][0]");
  EXPECT_STREQ(vpi_get_str(vpiFullName, select), "top.m[i][0]");
  vpiHandle of_element = vpi_handle(vpiTypespec, select);
  ASSERT_NE(of_element, nullptr);
  EXPECT_EQ(vpi_get(vpiType, of_element), vpiLogicTypespec);
  vpiHandle outer = vpi_handle(vpiParent, select);
  ASSERT_NE(outer, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, outer), "m[i]");
  vpiHandle of_subarray = vpi_handle(vpiTypespec, outer);
  ASSERT_NE(of_subarray, nullptr);
  EXPECT_EQ(vpi_get(vpiType, of_subarray), vpiArrayTypespec);
}

TEST_F(VarSelectsOfARun, ASelectThroughAnOutOfRangeVarSelectReadsX) {
  Run(TwoDimensional("0", 5));
  EXPECT_EQ(BinOf(Select()), "x");
}

TEST_F(VarSelectsOfARun, AnOutOfRangeSelectThroughAVarSelectReadsX) {
  Run(TwoDimensional("j", 1));
  EXPECT_EQ(BinOf(Select()), "x");
}

TEST_F(VarSelectsOfARun, ABitOfAVarSelectedElementKeepsTheGatesTerminals) {
  Run("module top; logic [3:0] p [2]; int i; wire y; logic c;\n"
      "  and g(y, p[i][2], c);\n"
      "endmodule\n");
  vpiHandle it = vpi_iterate(vpiPrimTerm, Named(vpiPrimitive, By("top"), "g"));
  int terms = 0;
  while (it != nullptr && vpi_scan(it) != nullptr) ++terms;
  EXPECT_EQ(terms, 3);
}

TEST_F(VarSelectsOfARun, AnOuterVarSelectHasItsFullName) {
  Run(TwoDimensional("0", 1));
  vpiHandle outer = vpi_handle(vpiParent, Select());
  ASSERT_NE(outer, nullptr);
  EXPECT_EQ(Str(vpiFullName, outer), "top.m[i]");
}

std::string PlacesDesign() {
  return "package pkg;\n"
         "  int pa[4], pb[4], pk;\n"
         "  function automatic void pf();\n"
         "    int fa[4]; int fk; fa[fk] = 1; pa[pk] = 1;\n"
         "  endfunction\n"
         "endpackage\n"
         "int ua[4], ub[4], uk;\n"
         "function automatic void uf();\n"
         "  int va[4]; int vk; va[vk] = 1; ua[uk] = 1;\n"
         "endfunction\n"
         "interface ifc; int ia[4]; int ik; initial ia[ik] = 1; endinterface\n"
         "program prg; int ra[4]; int rk; initial ra[rk] = 1; endprogram\n"
         "module top; ifc i(); prg p();\n"
         "  int ca[4], k; wire [31:0] w;\n"
         "  assign w = ca[k];\n"
         "  initial begin pkg::pb[k] = 1; ub[k] = 1; end\n"
         "  task run; int ta[4]; int tk; ta[tk] = 1; endtask\n"
         "  if (1) begin : g int ga[4]; int gk; initial ga[gk] = 1; end\n"
         "  class C; rand int ka[4], qa[4]; int kk; static int za[4];\n"
         "    function void set(); ka[kk] = 1; za[kk] = 1; endfunction\n"
         "    constraint c { foreach (qa[x]) qa[x] > 0; }\n"
         "  endclass\n"
         "endmodule\n";
}

TEST_F(VarSelectsOfARun, AVarSelectInAnInstanceOrGenerateBlockSelectsItsArray) {
  Run(PlacesDesign());
  ExpectSelectOf(By("top.i.ia"), "[ik]");
  ExpectSelectOf(By("top.p.ra"), "[rk]");
  ExpectSelectOf(By("top.g.ga"), "[gk]");
  ExpectSelectOf(By("top.ca"), "[k]");
}

TEST_F(VarSelectsOfARun, AVarSelectInAnInstanceIsNamedThroughIt) {
  Run(PlacesDesign());
  ExpectSelectNamed(By("top.i.ia"), "[ik]");
  ExpectSelectNamed(By("top.p.ra"), "[rk]");
  ExpectSelectNamed(By("top.ca"), "[k]");
}

TEST_F(VarSelectsOfARun, DISABLED_AVarSelectInAGenerateBlockIsNamedThroughIt) {
  Run(PlacesDesign());
  ExpectSelectNamed(By("top.g.ga"), "[gk]");
}

TEST_F(VarSelectsOfARun, AVarSelectOfAPackageOrUnitArraySelectsIt) {
  Run(PlacesDesign());
  vpiHandle unit = Named(vpiPackage, nullptr, "$unit");
  ASSERT_NE(unit, nullptr);
  ExpectNamedSelectOf(Named(vpiVariables, By("pkg"), "pa"), "[pk]");
  ExpectNamedSelectOf(Named(vpiVariables, By("pkg"), "pb"), "[k]");
  ExpectNamedSelectOf(Named(vpiVariables, unit, "ua"), "[uk]");
}

TEST_F(VarSelectsOfARun, DISABLED_AVarSelectInAModuleOfAUnitArraySelectsIt) {
  Run(PlacesDesign());
  vpiHandle unit = Named(vpiPackage, nullptr, "$unit");
  ASSERT_NE(unit, nullptr);
  ExpectNamedSelectOf(Named(vpiVariables, unit, "ub"), "[k]");
}

TEST_F(VarSelectsOfARun, AVarSelectInASubroutineSelectsItsLocalArray) {
  Run(PlacesDesign());
  vpiHandle pf = Named(vpiTaskFunc, By("pkg"), "pf");
  vpiHandle uf = Named(vpiTaskFunc, Named(vpiPackage, nullptr, "$unit"), "uf");
  vpiHandle run = Named(vpiTaskFunc, By("top"), "run");
  ASSERT_NE(pf, nullptr);
  ASSERT_NE(uf, nullptr);
  ASSERT_NE(run, nullptr);
  ExpectNamedSelectOf(Named(vpiVariables, pf, "fa"), "[fk]");
  ExpectNamedSelectOf(Named(vpiVariables, uf, "va"), "[vk]");
  ExpectNamedSelectOf(Named(vpiVariables, run, "ta"), "[tk]");
}

TEST_F(VarSelectsOfARun, AVarSelectInAClassSelectsItsPropertyArray) {
  Run(PlacesDesign());
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(defn, nullptr);
  ExpectSelectOf(Named(vpiVariables, defn, "ka"), "[kk]");
  ExpectSelectOf(Named(vpiVariables, defn, "qa"), "[x]");
  ExpectNamedSelectOf(Named(vpiVariables, defn, "za"), "[kk]");
  EXPECT_EQ(Str(vpiName, OnlySelectOf(Named(vpiVariables, defn, "ka"))),
            "ka[kk]");
  EXPECT_EQ(Str(vpiName, OnlySelectOf(Named(vpiVariables, defn, "qa"))),
            "qa[x]");
}

TEST_F(VarSelectsOfARun, DISABLED_AVarSelectOfANonStaticPropertyHasNoFullName) {
  Run(PlacesDesign());
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(defn, nullptr);
  for (const char* name : {"ka", "qa"}) {
    vpiHandle select = OnlySelectOf(Named(vpiVariables, defn, name));
    ASSERT_NE(select, nullptr) << name;
    EXPECT_EQ(vpi_get_str(vpiFullName, select), nullptr) << name;
  }
}

std::string ArrayKindsDesign() {
  return "module top; int d[], q[$], aa[int]; int k, x;\n"
         "  initial begin\n"
         "    d = {10, 11, 12}; q = {20, 21, 22}; aa = '{0: 30, 1: 31};\n"
         "    k = 1; x = d[k] + q[k] + aa[k];\n"
         "  end\n"
         "endmodule\n";
}

TEST_F(VarSelectsOfARun, AVarSelectOfADynamicQueueOrAssociativeArraySelectsIt) {
  Run(ArrayKindsDesign());
  for (const std::string kName : {"d", "q", "aa"}) {
    vpiHandle select = SelectOf(kName, "k");
    ASSERT_NE(select, nullptr) << kName;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, select)),
              VpiObjectOf(By("top." + kName)))
        << kName;
    EXPECT_EQ(Str(vpiFullName, select), "top." + kName + "[k]");
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiIndex, select)),
              VpiObjectOf(By("top.k")))
        << kName;
    EXPECT_EQ(vpi_get(vpiConstantSelect, select), 0) << kName;
  }
}

TEST_F(VarSelectsOfARun,
       DISABLED_AVarSelectOfADynamicQueueOrAssociativeArrayReadsAndWritesIt) {
  Run(ArrayKindsDesign());
  const std::vector<std::string> kNames = {"d", "q", "aa"};
  const std::vector<int> kFirsts = {10, 20, 30};
  for (size_t at = 0; at < kNames.size(); ++at) {
    vpiHandle select = SelectOf(kNames[at], "k");
    ASSERT_NE(select, nullptr) << kNames[at];
    EXPECT_EQ(IntegerOf(select), kFirsts[at] + 1) << kNames[at];
    PutInt(select, 99);
    EXPECT_EQ(IntegerOf(select), 99) << kNames[at];
  }
  PutInt(By("top.k"), 0);
  for (size_t at = 0; at < kNames.size(); ++at) {
    EXPECT_EQ(IntegerOf(SelectOf(kNames[at], "k")), kFirsts[at]) << kNames[at];
  }
}

std::string NestedDesign() {
  return "module top; logic m [2][2]; int i, j; wire y; logic c;\n"
         "  and g(y, m[i][j], c);\n"
         "  initial begin\n"
         "    m[0][0] = 0; m[0][1] = 1; m[1][0] = 1; m[1][1] = 0; i = 1; j = "
         "0;\n"
         "  end\n"
         "endmodule\n";
}

TEST_F(VarSelectsOfARun,
       AWriteThroughASelectOfAVarSelectChangesOnlyItsElement) {
  Run(NestedDesign());
  vpiHandle select = Select();
  ASSERT_NE(select, nullptr);
  ASSERT_EQ(ElementsOfM(), "0110");
  PutInt(select, 0);
  EXPECT_EQ(ElementsOfM(), "0100");
}

TEST_F(VarSelectsOfARun, AVarSelectHandleFollowsItsIndex) {
  Run(Design("int i;", "i = 1;"));
  vpiHandle select = Select();
  ASSERT_NE(select, nullptr);
  EXPECT_EQ(BinOf(select), "1");
  PutInt(By("top.i"), 0);
  EXPECT_EQ(BinOf(select), "0");
  PutInt(select, 1);
  EXPECT_EQ(BinOf(By("top.v[0]")) + BinOf(By("top.v[1]")), "11");
}

TEST_F(VarSelectsOfARun, ASelectOfAVarSelectHandleFollowsBothIndices) {
  Run(NestedDesign());
  vpiHandle select = Select();
  ASSERT_NE(select, nullptr);
  EXPECT_EQ(BinOf(select), "1");
  PutInt(By("top.i"), 0);
  EXPECT_EQ(BinOf(select), "0");
  PutInt(By("top.j"), 1);
  EXPECT_EQ(BinOf(select), "1");
  PutInt(select, 0);
  EXPECT_EQ(ElementsOfM(), "0010");
}

TEST_F(VarSelectsOfARun, APutThroughAnOutOfRangeIndexWritesNothing) {
  Run(Design("int i;", "i = 5;"));
  vpiHandle select = Select();
  ASSERT_NE(select, nullptr);
  for (int value : {0, 1}) {
    PutInt(select, value);
    EXPECT_EQ(BinOf(By("top.v[0]")) + BinOf(By("top.v[1]")), "01") << value;
  }
}

TEST_F(VarSelectsOfARun, APutThroughAnIndexHoldingXWritesNothing) {
  Run(Design("integer i;", ""));
  vpiHandle select = Select();
  ASSERT_NE(select, nullptr);
  for (int value : {0, 1}) {
    PutInt(select, value);
    EXPECT_EQ(BinOf(By("top.v[0]")) + BinOf(By("top.v[1]")), "01") << value;
  }
}

TEST_F(VarSelectsOfARun, APutThroughEitherIndexNamingNoElementWritesNothing) {
  Run(NestedDesign());
  vpiHandle select = Select();
  ASSERT_NE(select, nullptr);
  for (const char* index : {"top.i", "top.j"}) {
    PutInt(By("top.i"), 1);
    PutInt(By("top.j"), 0);
    PutInt(By(index), 5);
    for (int value : {0, 1}) {
      PutInt(select, value);
      EXPECT_EQ(ElementsOfM(), "0110") << index << " " << value;
    }
  }
}

TEST_F(VarSelectsOfARun,
       DISABLED_AConstantIndexIntoAQueueOrAssociativeArrayIsNoConstantSelect) {
  Run("module top; int q[$], aa[int], sa[4];\n"
      "  initial begin q = {1, 2, 3}; q[1] = 5; aa[2] = 5; sa[2] = 5; end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kLhs = LhsOf(By("top"));
  ASSERT_EQ(kLhs.size(), 4U);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kLhs[1]), 0);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kLhs[2]), 0);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kLhs[3]), 1);
}

TEST_F(VarSelectsOfARun,
       DISABLED_AConstantIndexIntoAnAutomaticArrayIsNoConstantSelect) {
  Run("module top;\n"
      "  function automatic void af(); int la[4]; la[1] = 5; endfunction\n"
      "  function void sf(); int la[4]; la[1] = 5; endfunction\n"
      "endmodule\n");
  const std::vector<vpiHandle> kAutomatic = SubroutineLhsOf("af");
  const std::vector<vpiHandle> kStatic = SubroutineLhsOf("sf");
  ASSERT_EQ(kAutomatic.size(), 1U);
  ASSERT_EQ(kStatic.size(), 1U);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kAutomatic[0]), 0);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kStatic[0]), 1);
}

TEST_F(VarSelectsOfARun, OneVaryingIndexMakesAMultiIndexSelectNonConstant) {
  Run("module top; logic m [2][2]; int i, j;\n"
      "  initial begin m[1][j] = 1; m[i][1] = 1; m[1][0] = 1; end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kLhs = LhsOf(By("top"));
  ASSERT_EQ(kLhs.size(), 3U);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kLhs[0]), 0);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kLhs[1]), 0);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kLhs[2]), 1);
}

TEST_F(VarSelectsOfARun, AnElaborationConstantIndexIsAConstantSelect) {
  Run("module top; parameter P = 1; int a[4];\n"
      "  initial begin a[P] = 1; a[P + 1] = 2; end\n"
      "  for (genvar g = 0; g < 2; g++) begin : gen\n"
      "    initial a[g] = 3;\n"
      "  end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kLhs = LhsOf(By("top"));
  ASSERT_GE(kLhs.size(), 2U);
  for (vpiHandle lhs : kLhs) EXPECT_EQ(vpi_get(vpiConstantSelect, lhs), 1);
  const std::vector<vpiHandle> kInGenerate = LhsOf(By("top.gen[1]"));
  ASSERT_EQ(kInGenerate.size(), 1U);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kInGenerate[0]), 1);
}

std::string ElementTypesDesign() {
  return "module top;\n"
         "  typedef struct packed { int i1; bit [3:0] b; } pst;\n"
         "  typedef enum logic [1:0] { A, B } et;\n"
         "  int ia[4]; pst sa[2]; et ea[2]; int k;\n"
         "  byte d[]; shortint sq[$]; bit [4:0] sx[int];\n"
         "  initial begin\n"
         "    ia[k] = 1; sa[k] = '0; ea[k] = A;\n"
         "    d = new[2]; sq = {1, 2}; d[k] = 1; sq[k] = 1; sx[k] = 1;\n"
         "  end\n"
         "endmodule\n";
}

TEST_F(VarSelectsOfARun, AVarSelectsTypespecIsItsElementsType) {
  Run(ElementTypesDesign());
  const std::vector<std::string> kNames = {"ia", "sa", "ea", "d", "sq", "sx"};
  const std::vector<int> kKinds = {vpiIntTypespec,      vpiStructTypespec,
                                   vpiEnumTypespec,     vpiByteTypespec,
                                   vpiShortIntTypespec, vpiBitTypespec};
  for (size_t at = 0; at < kNames.size(); ++at) {
    vpiHandle select = SelectOf(kNames[at], "k");
    ASSERT_NE(select, nullptr) << kNames[at];
    EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiTypespec, select)), kKinds[at])
        << kNames[at];
  }
  EXPECT_EQ(Str(vpiName, vpi_handle(vpiTypespec, SelectOf("sa", "k"))), "pst");
  EXPECT_EQ(Str(vpiName, vpi_handle(vpiTypespec, SelectOf("ea", "k"))), "et");
}

TEST_F(VarSelectsOfARun, AVarSelectsSizeIsItsElementsWidth) {
  Run(ElementTypesDesign());
  ExpectSelectWidths({"ia", "sa", "ea"}, {32, 36, 2});
}

TEST_F(VarSelectsOfARun,
       DISABLED_AVarSelectOfADynamicQueueOrAssociativeArrayIsItsElementsWidth) {
  Run(ElementTypesDesign());
  ExpectSelectWidths({"d", "sq", "sx"}, {8, 16, 5});
}

TEST_F(VarSelectsOfARun, AVarSelectsIndexIsTheExpressionWritten) {
  Run("module top; int a[8], aa[int]; int i;\n"
      "  initial begin a[i + 1] = 1; aa[i] = 1; end\n"
      "endmodule\n");
  vpiHandle sum = vpi_handle(vpiIndex, OnlySelectOf(By("top.a")));
  ASSERT_NE(sum, nullptr);
  EXPECT_EQ(vpi_get(vpiType, sum), vpiOperation);
  EXPECT_EQ(OpOf(sum), vpiAddOp);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiIndex, OnlySelectOf(By("top.aa")))),
            VpiObjectOf(By("top.i")));
}

TEST(VariableSelectModel, ASelectWithNoParentIsNoConstantSelect) {
  EXPECT_FALSE(VpiVarSelectConstantSelectOf(nullptr));
  VpiObject index;
  index.type = vpiConstant;
  VpiObject driver;
  driver.type = vpiForce;
  VpiObject select;
  select.type = vpiVarSelect;
  select.children = {&driver, &index};
  EXPECT_FALSE(VpiVarSelectConstantSelectOf(&select));
}

}  // namespace
}  // namespace delta
