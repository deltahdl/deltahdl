#include <gtest/gtest.h>

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

// Detail 1: vpiConstantSelect of a var select is TRUE only when every one of the
// three conditions holds - all index expressions are elaboration-time
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

}  // namespace
}  // namespace delta
