#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

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
  EXPECT_EQ(vpi_get(vpiConstantSelect, &select_), 1);
}

// Detail 1, first condition: an index expression that is not an
// elaboration-time constant makes the select non-constant.
TEST_F(VariableSelectObject, ANonConstantIndexMakesTheSelectNonConstant) {
  index_.type = vpiOperation;

  EXPECT_EQ(vpi_get(vpiConstantSelect, &select_), 0);
}

// Detail 1, second condition: an array whose bounds are not static - a queue,
// a dynamic array or an associative array - is not the parent the rule wants.
TEST_F(VariableSelectObject, ADynamicallyBoundedParentMakesItNonConstant) {
  array_.array_type = vpiDynamicArray;

  EXPECT_EQ(vpi_get(vpiConstantSelect, &select_), 0);
}

// Detail 1, third condition: the parent has to be a constant select itself, and
// an array var of automatic lifetime is not one.
TEST_F(VariableSelectObject, AnAutomaticParentMakesItNonConstant) {
  array_.automatic = true;

  EXPECT_EQ(vpi_get(vpiConstantSelect, &select_), 0);
}

// Detail 1 read down a chain of selects. The second condition names what the
// prefix has to be - "an unpacked array with static bounds" - so a select whose
// prefix is another select is not a constant select however constant its own
// index is, while the select directly over the array is one.
TEST_F(VariableSelectObject, ASelectOfASelectIsNotAConstantSelect) {
  VpiObject outer_index;
  outer_index.type = vpiConstant;
  VpiObject outer;
  outer.type = vpiVarSelect;
  outer.parent = &array_;
  outer.children = {&outer_index};

  select_.parent = &outer;

  EXPECT_EQ(vpi_get(vpiConstantSelect, &outer), 1);
  EXPECT_EQ(vpi_get(vpiConstantSelect, &select_), 0);
}

// The property belongs to the var select. An object of another kind reports 0
// here, its own clause owning what a constant selection means for it.
TEST_F(VariableSelectObject, TheRuleAnswersForAVarSelectAlone) {
  EXPECT_EQ(vpi_get(vpiConstantSelect, &array_), 0);
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

  std::vector<vpiHandle> seen = ScanAll(vpi_iterate(vpiIndex, &select_));
  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], &index_);
  EXPECT_EQ(seen[1], &second);
}

}  // namespace
}  // namespace delta
