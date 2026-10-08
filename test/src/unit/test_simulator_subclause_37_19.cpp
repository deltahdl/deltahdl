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

// §37.19 Variable select: the VPI object model for a var select - a variable
// reference qualified by one or more index expressions (vpiIndex) that reach
// into an unpacked array var (its vpiParent). The diagram's name, full name,
// size, value and typespec relations are the generic variable machinery carried
// by §37.17, §37.3 and the Clause 38 routines; the one normative rule the
// subclause's text defines is Detail 1, the vpiConstantSelect property. These
// tests observe the production helper in vpi.cpp that applies that rule.

// Detail 1: vpiConstantSelect of a var select is TRUE only when every one of
// the three conditions holds - all index expressions are elaboration-time
// constants, the parent is an unpacked array with static bounds, and the parent
// is itself a constant select. When all three hold the property is TRUE, and
// dropping any single condition makes it FALSE.
TEST(VariableSelectModel, ConstantSelectRequiresAllThreeConditions) {
  VpiVarSelectConstantSelectQuery all_true;
  all_true.all_indices_constant = true;
  all_true.parent_is_unpacked_static_array = true;
  all_true.parent_constant_select = true;
  EXPECT_TRUE(VpiVarSelectConstantSelect(all_true));

  // An index expression is not an elaboration-time constant -> FALSE.
  VpiVarSelectConstantSelectQuery q1 = all_true;
  q1.all_indices_constant = false;
  EXPECT_FALSE(VpiVarSelectConstantSelect(q1));

  // The parent is not an unpacked array with static bounds -> FALSE.
  VpiVarSelectConstantSelectQuery q2 = all_true;
  q2.parent_is_unpacked_static_array = false;
  EXPECT_FALSE(VpiVarSelectConstantSelect(q2));

  // The parent is not itself a constant select -> FALSE.
  VpiVarSelectConstantSelectQuery q3 = all_true;
  q3.parent_constant_select = false;
  EXPECT_FALSE(VpiVarSelectConstantSelect(q3));
}

// The figure's own reading of the same detail. §37.4.2 reads "bool:
// vpiConstantSelect" with vpi_get(), so the property is answered through the
// public routine on a var select object rather than from a query struct a
// caller filled in; the rule was applied by a helper nothing called, so
// vpi_get(vpiConstantSelect, sel) reported 0 whatever the select was.
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

// Detail 1, all three conditions met on the object: a constant index into a
// static unpacked array whose own lifetime is static.
TEST_F(VariableSelectObject, AConstantIndexIntoAStaticArrayIsAConstantSelect) {
  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&select_)), 1);
}

// Detail 1, first condition: an index expression that is not an
// elaboration-time constant makes the select non-constant.
TEST_F(VariableSelectObject, ANonConstantIndexMakesTheSelectNonConstant) {
  index_.type = vpiOperation;

  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&select_)), 0);
}

// Detail 1, second condition: an array whose bounds are not static - a queue,
// a dynamic array or an associative array - is not the parent the rule wants.
TEST_F(VariableSelectObject, ADynamicallyBoundedParentMakesItNonConstant) {
  array_.array_type = vpiDynamicArray;

  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&select_)), 0);
}

// Detail 1, third condition: the parent has to be a constant select itself, and
// an array var of automatic lifetime is not one.
TEST_F(VariableSelectObject, AnAutomaticParentMakesItNonConstant) {
  array_.automatic = true;

  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&select_)), 0);
}

// Detail 1 read down a chain of selects. The second condition names what the
// prefix has to be - an unpacked array whose bounds are fixed - so a select
// whose prefix is another select is not a constant select however constant its
// own index is, while the select directly over the array is one.
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

// The rule is the var select's. The array it selects into is answered by its
// own clause instead: §37.17 detail 27 makes a variable of static lifetime with
// no parent a constant select, which the var select's rule, wanting a parent
// that is an unpacked array, would never make it.
TEST_F(VariableSelectObject, TheArrayIsAnsweredByTheVariablesRule) {
  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&array_)), 1);
}

// The figure's vpiIndex relation, which §37.4.3 walks with vpi_iterate() and
// vpi_scan(). The relation was recognized for no reference object of this kind,
// so the index expressions a select was written with were reachable from it by
// nothing.
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

// The var selects of a run: the second terminal of the gate g of top, written
// as an element of the array var v selected by an index that varies.
class VarSelectsOfARun : public VpiDesignRun {
 protected:
  // The design whose g selects v[i], i declared by `decls` and set by
  // `setup` once v holds 0 and 1.
  static std::string Design(const std::string& decls,
                            const std::string& setup) {
    return "module top; logic v [2]; " + decls +
           " wire y; logic c;\n"
           "  and g(y, v[i], c);\n"
           "  initial begin v[0] = 0; v[1] = 1; " +
           setup + " end\nendmodule\n";
  }

  // What the second terminal of g reaches through vpiExpr.
  static vpiHandle Select() {
    vpiHandle it =
        vpi_iterate(vpiPrimTerm, Named(vpiPrimitive, By("top"), "g"));
    if (it == nullptr) return nullptr;
    vpi_scan(it);
    vpiHandle term = vpi_scan(it);
    vpi_free_object(it);
    return term == nullptr ? nullptr : vpi_handle(vpiExpr, term);
  }

  // The value of `obj` as a binary string.
  static std::string BinOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiBinStrVal;
    vpi_get_value(obj, &value);
    return value.format == vpiBinStrVal && value.value.str != nullptr
               ? std::string(value.value.str)
               : std::string();
  }
};

// §37.19: an element of an array var selected by an index that varies is a
// var select, reaching the array through vpiParent and the index expression
// through vpiIndex, and not a constant select (detail 1). It reached nothing.
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

// §37.19 with §38.15 and §38.34: a var select reads the element its index
// names when read, and a put writes that element.
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

// §11.5.1: a read through an index outside the array yields the default of a
// 4-state element, x...
TEST_F(VarSelectsOfARun, AVarSelectWhoseIndexIsOutOfRangeReadsX) {
  Run(Design("int i;", "i = 5;"));
  EXPECT_EQ(BinOf(Select()), "x");
}

// ...and so does a read through an index holding x.
TEST_F(VarSelectsOfARun, AVarSelectWhoseIndexHoldsXReadsX) {
  Run(Design("integer i;", ""));
  EXPECT_EQ(BinOf(Select()), "x");
}

// The design whose g selects m[i][`inner`] of a two-dimensional array, i set
// to `outer` once m[1][0] holds 1.
std::string TwoDimensional(const std::string& inner, int outer) {
  return "module top; logic m [2][2]; int i, j; wire y; logic c;\n"
         "  and g(y, m[i][" +
         inner +
         "], c);\n"
         "  initial begin m[0][0] = 0; m[1][0] = 1; j = 5; i = " +
         std::to_string(outer) + "; end\nendmodule\n";
}

// §37.19: a select through a var select of a subarray is a var select whose
// vpiParent is that var select, and no constant select (detail 1). It reads
// the element both indices name. It reached nothing.
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

// §11.5.1: an outer index outside the array leaves the select no element, and
// it reads x...
TEST_F(VarSelectsOfARun, ASelectThroughAnOutOfRangeVarSelectReadsX) {
  Run(TwoDimensional("0", 5));
  EXPECT_EQ(BinOf(Select()), "x");
}

// ...and so does an inner index outside the subarray.
TEST_F(VarSelectsOfARun, AnOutOfRangeSelectThroughAVarSelectReadsX) {
  Run(TwoDimensional("j", 1));
  EXPECT_EQ(BinOf(Select()), "x");
}

// A var select of an element that is a vector selects no subarray, so a
// further index selects a bit of the element, not a var select; the gate
// still has a prim term per terminal.
TEST_F(VarSelectsOfARun, ABitOfAVarSelectedElementKeepsTheGatesTerminals) {
  Run("module top; logic [3:0] p [2]; int i; wire y; logic c;\n"
      "  and g(y, p[i][2], c);\n"
      "endmodule\n");
  vpiHandle it = vpi_iterate(vpiPrimTerm, Named(vpiPrimitive, By("top"), "g"));
  int terms = 0;
  while (it != nullptr && vpi_scan(it) != nullptr) ++terms;
  EXPECT_EQ(terms, 3);
}

}  // namespace
}  // namespace delta
