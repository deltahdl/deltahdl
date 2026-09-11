#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.58 Simple expressions: the VPI object model for a simple expression - a
// reference (net, variable, ref obj, parameter, spec param) or a select of one
// (var select, bit select). The name/full-name strings and the value relation
// are the generic naming machinery carried by §38.11; the subclause's own
// normative rules are its three numbered Details - the content of the vpiUse
// relation for a vector and for a bit-select, and the vpiConstantSelect
// property of a bit-select. The vpiParent and vpiIndex relations the figure
// draws from a bit select are this clause's too, because a relation named for
// the edge reaches nothing without a rule that says what it reaches. These
// tests observe the production code that applies all of those.

// Detail 1: for a vector simple expression, the vpiUse relation reaches every
// use of the vector itself together with every use of any of the vector's
// part-selects or bit-selects. A candidate use is therefore accessed when it
// references the vector or either kind of derived select, and only an
// unrelated use is excluded.
TEST(SimpleExpressionModel, VectorUseReachesVectorPartSelectsAndBitSelects) {
  // A use of the vector itself is accessed.
  EXPECT_TRUE(VpiSimpleExprVectorUseAccessesUse(
      /*references_vector=*/true, /*references_part_select_of_vector=*/false,
      /*references_bit_select_of_vector=*/false));
  // A use of one of the vector's part-selects is accessed.
  EXPECT_TRUE(VpiSimpleExprVectorUseAccessesUse(false, true, false));
  // A use of one of the vector's bit-selects is accessed.
  EXPECT_TRUE(VpiSimpleExprVectorUseAccessesUse(false, false, true));
  // A use that references none of those is not accessed.
  EXPECT_FALSE(VpiSimpleExprVectorUseAccessesUse(false, false, false));
}

// Detail 2: for a bit-select, the vpiUse relation reaches every specific use of
// that bit, every use of the parent vector, and every part-select of the parent
// that contains the bit. Each of those three independently makes a use
// accessed, and a use that matches none of them is excluded.
TEST(SimpleExpressionModel, BitSelectUseReachesBitParentAndContainingSelect) {
  // A specific use of the bit itself is accessed.
  EXPECT_TRUE(VpiSimpleExprBitSelectUseAccessesUse(
      /*references_this_bit=*/true, /*references_parent_vector=*/false,
      /*references_part_select_containing_bit=*/false));
  // A use of the parent vector is accessed.
  EXPECT_TRUE(VpiSimpleExprBitSelectUseAccessesUse(false, true, false));
  // A use of a part-select of the parent that contains the bit is accessed.
  EXPECT_TRUE(VpiSimpleExprBitSelectUseAccessesUse(false, false, true));
  // A use matching none of the three is not accessed. (For example, a
  // part-select of the parent that does not contain this bit.)
  EXPECT_FALSE(VpiSimpleExprBitSelectUseAccessesUse(false, false, false));
}

// Detail 3: vpiConstantSelect of a bit-select is TRUE only when both conditions
// hold - every associated index expression is an elaboration-time constant and
// vpiConstantSelect is itself TRUE for the bit-select's parent. When both hold
// the property is TRUE, and dropping either condition makes it FALSE.
TEST(SimpleExpressionModel, BitSelectConstantSelectRequiresBothConditions) {
  EXPECT_TRUE(VpiSimpleExprBitSelectConstantSelect(
      /*all_indices_constant=*/true, /*parent_constant_select=*/true));

  // An index expression is not an elaboration-time constant -> FALSE.
  EXPECT_FALSE(VpiSimpleExprBitSelectConstantSelect(false, true));

  // The parent is not itself a constant select -> FALSE.
  EXPECT_FALSE(VpiSimpleExprBitSelectConstantSelect(true, false));

  // Neither condition holds -> FALSE.
  EXPECT_FALSE(VpiSimpleExprBitSelectConstantSelect(false, false));
}

// Detail 3 through the figure's own reading. §37.4.2 reads "bool:
// vpiConstantSelect" with vpi_get(), so the property is answered on a bit
// select object rather than from booleans a caller worked out; the rule was
// applied by a helper nothing called, so the property read 0 whatever the
// select was.
class BitSelectObject : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    vector_.type = vpiIntegerVar;
    index_.type = vpiConstant;
    select_.type = vpiBitSelect;
    select_.parent = &vector_;
    select_.children = {&index_};
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  std::vector<vpiHandle> ScanAll(vpiHandle it) {
    std::vector<vpiHandle> seen;
    if (it == nullptr) return seen;
    while (vpiHandle h = vpi_scan(it)) seen.push_back(h);
    return seen;
  }

  VpiObject vector_;
  VpiObject index_;
  VpiObject select_;
  VpiContext ctx_;
};

// Detail 3, both conditions met: a constant index into a vector of static
// lifetime.
TEST_F(BitSelectObject, AConstantIndexIntoAStaticVectorIsAConstantSelect) {
  EXPECT_EQ(vpi_get(vpiConstantSelect, &select_), 1);
}

// Detail 3, first condition: an index that is not an elaboration-time constant.
TEST_F(BitSelectObject, ANonConstantIndexMakesTheSelectNonConstant) {
  index_.type = vpiOperation;

  EXPECT_EQ(vpi_get(vpiConstantSelect, &select_), 0);
}

// Detail 3, second condition: the prefix has to be a constant select itself,
// and a vector of automatic lifetime is not one.
TEST_F(BitSelectObject, AnAutomaticPrefixMakesTheSelectNonConstant) {
  vector_.automatic = true;

  EXPECT_EQ(vpi_get(vpiConstantSelect, &select_), 0);
}

// The figure's vpiParent edge, drawn from the bit select to the class grouping
// a var select, an integer var, a time var, a parameter and a spec param.
// vpiParent is a tag no object's type is, so the traversal the relation fell
// through to reached the vector from none of its bit-selects.
TEST_F(BitSelectObject, ParentReachesTheVectorSelectedInto) {
  EXPECT_EQ(vpi_handle(vpiParent, &select_), &vector_);
}

// The figure's vpiIndex edge, drawn from the bit select to expr and walked with
// vpi_iterate()/vpi_scan() (§37.4.3). It was recognized for no reference object
// of this kind, so the index a select was written with was reachable from it by
// nothing.
TEST_F(BitSelectObject, IndexReachesTheSelectsIndexExpression) {
  std::vector<vpiHandle> seen = ScanAll(vpi_iterate(vpiIndex, &select_));
  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(seen[0], &index_);
}

}  // namespace
}  // namespace delta
