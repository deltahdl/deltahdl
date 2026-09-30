#include <gtest/gtest.h>

#include "elaborator/concurrent_assertion_expr.h"
#include "elaborator/function_in_checker.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

// §17.8, end to end: the actual-argument carve-out realized from real source.
// A checker declares a free variable (the `rand` checker variable of §17.7) and
// passes it as the actual argument to a function used in the checker. Because
// §17.8 forbids the carve-out only for a function's formal arguments and its
// internal variables — never for the value supplied at the call site — the
// elaborator must admit this. The called function is automatic, takes an
// input-only argument, and has no side effects, so it also satisfies the §16.6
// restrictions that §17.8 imposes on a function call feeding a checker variable
// assignment; the free variable appearing only as the actual argument is what
// §17.8 permits here.
TEST(FunctionInChecker, FreeVariableAsActualArgumentElaboratesCleanly) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(bit valid);\n"
      "  rand bit flag;\n"
      "  function automatic bit pass_through(bit x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  bit observed;\n"
      "  assign observed = pass_through(flag);\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
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

// §17.8 with §16.6: a function called on the right-hand side of a checker
// variable assignment shall have no output, inout or ref argument, a const
// ref being allowed. Calls of f, g and h, which have one each, are reported
// in nonblocking and blocking assignments; k, whose ref is const, and the
// input-only p are not.
TEST(FunctionInChecker, WritingArgumentCallOnAssignmentRhsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(logic a, logic clk);\n"
      "  bit z, w, v, t, u, q;\n"
      "  function automatic bit f(input bit x, output bit o);\n"
      "    o = ~x; return x;\n"
      "  endfunction\n"
      "  function automatic bit g(inout bit io); return io; endfunction\n"
      "  function automatic bit h(ref bit r); return r; endfunction\n"
      "  function automatic bit k(input bit x, const ref bit c);\n"
      "    return x & c;\n"
      "  endfunction\n"
      "  function bit p(bit x); return x; endfunction\n"
      "  always_ff @(posedge clk) z <= f(a, t);\n"
      "  always_ff @(posedge clk) w <= g(u) | k(a, q);\n"
      "  always_comb v = h(q) ^ p(a);\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "function 'f' has an output",
                            12, "17.8"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "function 'g' has an output",
                            13, "17.8"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "function 'h' has an output",
                            14, "17.8"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

}  // namespace
