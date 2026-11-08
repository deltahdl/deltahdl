#include <gtest/gtest.h>

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

TEST_F(VariableSelectObject, AnAutomaticParentMakesItNonConstant) {
  array_.automatic = true;

  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&select_)), 0);
}

TEST_F(VariableSelectObject, ASelectOfASelectIsNotAConstantSelect) {
  VpiObject outer_index;
  outer_index.type = vpiConstant;
  VpiObject outer;
  outer.type = vpiVarSelect;
  outer.parent = &array_;
  outer.children = {&outer_index};

  select_.parent = &outer;

  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&outer)), 1);
  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&select_)), 0);
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
