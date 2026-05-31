#include <gtest/gtest.h>

#include "elaborator/function_in_checker.h"

using namespace delta;

namespace {

TEST(FunctionInChecker, FormalAndInternalVariablesCannotBeFreeVariables) {
  // §17.8: the formal arguments and internal variables of functions used in
  // checkers shall not be declared as free variables.
  EXPECT_FALSE(CheckerFunctionFreeVariableAllowed(
      CheckerFunctionFreeVariablePosition::kFormalArgument));
  EXPECT_FALSE(CheckerFunctionFreeVariableAllowed(
      CheckerFunctionFreeVariablePosition::kInternalVariable));
}

TEST(FunctionInChecker, FreeVariableMayBePassedAsActualArgument) {
  // §17.8: free variables are allowed to be passed in as actual arguments to a
  // function.
  EXPECT_TRUE(CheckerFunctionFreeVariableAllowed(
      CheckerFunctionFreeVariablePosition::kActualArgument));
}

TEST(FunctionInChecker, AssignmentRhsCallAllowedWhenAssertionRestrictionsMet) {
  // §17.8: a function call on the RHS of a checker variable assignment is
  // permitted when it satisfies the §16.6 restrictions — here an input-only,
  // automatic, side-effect-free function.
  EXPECT_TRUE(CheckerVariableAssignmentFunctionCallAllowed(
      FunctionArgKind::kInput, /*is_automatic=*/true,
      /*preserves_no_state=*/false, /*has_no_side_effects=*/true));
  // const ref is explicitly permitted by §16.6, and a stateless static
  // function with no side effects is equally acceptable.
  EXPECT_TRUE(CheckerVariableAssignmentFunctionCallAllowed(
      FunctionArgKind::kConstRef, /*is_automatic=*/false,
      /*preserves_no_state=*/true, /*has_no_side_effects=*/true));
}

TEST(FunctionInChecker, AssignmentRhsCallRejectedOnArgKindViolation) {
  // §17.8 inherits §16.6: output, inout, and ref arguments disqualify the call
  // even when the function is otherwise eligible.
  EXPECT_FALSE(CheckerVariableAssignmentFunctionCallAllowed(
      FunctionArgKind::kOutput, /*is_automatic=*/true,
      /*preserves_no_state=*/false, /*has_no_side_effects=*/true));
  EXPECT_FALSE(CheckerVariableAssignmentFunctionCallAllowed(
      FunctionArgKind::kInout, /*is_automatic=*/true,
      /*preserves_no_state=*/false, /*has_no_side_effects=*/true));
  EXPECT_FALSE(CheckerVariableAssignmentFunctionCallAllowed(
      FunctionArgKind::kRef, /*is_automatic=*/true,
      /*preserves_no_state=*/false, /*has_no_side_effects=*/true));
}

TEST(FunctionInChecker, AssignmentRhsCallRejectedOnEligibilityViolation) {
  // §17.8 inherits §16.6: a function that is neither automatic nor stateless,
  // or one that has side effects, is not eligible regardless of argument kind.
  EXPECT_FALSE(CheckerVariableAssignmentFunctionCallAllowed(
      FunctionArgKind::kInput, /*is_automatic=*/false,
      /*preserves_no_state=*/false, /*has_no_side_effects=*/true));
  EXPECT_FALSE(CheckerVariableAssignmentFunctionCallAllowed(
      FunctionArgKind::kInput, /*is_automatic=*/true,
      /*preserves_no_state=*/false, /*has_no_side_effects=*/false));
}

}  // namespace
