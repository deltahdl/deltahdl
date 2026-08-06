#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.58 Simple expressions: the VPI object model for a simple expression - a
// reference (net, variable, ref obj, parameter, spec param) or a select of one
// (var select, bit select). The diagram's vpiParent and vpiIndex relations, the
// name/full-name strings, and the value relation are the generic traversal and
// naming machinery carried by §38.18 and §38.11; the subclause's own normative
// rules are its three numbered Details - the content of the vpiUse relation for
// a vector and for a bit-select, and the vpiConstantSelect property of a
// bit-select. These tests observe the production helpers in vpi.cpp that apply
// those rules.

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

}  // namespace
}  // namespace delta
