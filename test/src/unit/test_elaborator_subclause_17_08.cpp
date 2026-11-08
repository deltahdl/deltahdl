#include <gtest/gtest.h>

#include "elaborator/concurrent_assertion_expr.h"
#include "elaborator/function_in_checker.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(FunctionInChecker, FormalAndInternalVariablesCannotBeFreeVariables) {
  EXPECT_FALSE(CheckerFunctionFreeVariableAllowed(
      CheckerFunctionFreeVariablePosition::kFormalArgument));
  EXPECT_FALSE(CheckerFunctionFreeVariableAllowed(
      CheckerFunctionFreeVariablePosition::kInternalVariable));
}

TEST(FunctionInChecker, FreeVariableMayBePassedAsActualArgument) {
  EXPECT_TRUE(CheckerFunctionFreeVariableAllowed(
      CheckerFunctionFreeVariablePosition::kActualArgument));
}

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
  EXPECT_TRUE(CheckerVariableAssignmentFunctionCallAllowed(
      FunctionArgKind::kInput, true, false, true));
  EXPECT_TRUE(CheckerVariableAssignmentFunctionCallAllowed(
      FunctionArgKind::kConstRef, false, true, true));
}

TEST(FunctionInChecker, AssignmentRhsCallRejectedOnArgKindViolation) {
  EXPECT_FALSE(CheckerVariableAssignmentFunctionCallAllowed(
      FunctionArgKind::kOutput, true, false, true));
  EXPECT_FALSE(CheckerVariableAssignmentFunctionCallAllowed(
      FunctionArgKind::kInout, true, false, true));
  EXPECT_FALSE(CheckerVariableAssignmentFunctionCallAllowed(
      FunctionArgKind::kRef, true, false, true));
}

TEST(FunctionInChecker, AssignmentRhsCallRejectedOnEligibilityViolation) {
  EXPECT_FALSE(CheckerVariableAssignmentFunctionCallAllowed(
      FunctionArgKind::kInput, false, false, true));
  EXPECT_FALSE(CheckerVariableAssignmentFunctionCallAllowed(
      FunctionArgKind::kInput, true, false, false));
}

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

TEST(CheckerFunctionCalls,
     AFunctionWithASideEffectOnTheRightHandSideIsReported) {
  const char* const kReport =
      "keeps state or has a side effect and cannot be called on the "
      "right-hand side of a checker variable assignment";
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk, input int a);\n"
      "  int count;\n"
      "  int v, w;\n"
      "  function int bump(int x);\n"
      "    count = x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  function automatic int twice(int x);\n"
      "    return x + x;\n"
      "  endfunction\n"
      "  always_ff @(posedge clk) v <= bump(a);\n"
      "  always_ff @(posedge clk) w <= twice(a);\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 11, "17.8"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 12, "17.8"));
}

TEST(CheckerFunctionCalls, AnOutsideFunctionOnTheRightHandSideIsChecked) {
  const char* const kReport =
      "writes an argument back, keeps state or has a side effect and cannot "
      "be called on the right-hand side of a checker variable assignment";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int count;\n"
      "  function int bump(int x);\n"
      "    count = count + 1;\n"
      "    return x;\n"
      "  endfunction\n"
      "  function automatic int peek(input int x, output int y);\n"
      "    y = x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  function automatic int twice(int x);\n"
      "    return x + x;\n"
      "  endfunction\n"
      "  checker c(logic clk, int a);\n"
      "    int v, w, z, out;\n"
      "    always_ff @(posedge clk) v <= bump(a);\n"
      "    always_ff @(posedge clk) w <= peek(a, out);\n"
      "    always_ff @(posedge clk) z <= twice(a);\n"
      "  endchecker\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 16, "17.8"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 17, "17.8"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 18, "17.8"));
}

}  // namespace
